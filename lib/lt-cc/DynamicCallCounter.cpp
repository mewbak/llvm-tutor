//========================================================================
// FILE:
//    DynamicCallCounter.cpp
//
// AUTHOR:
//    banach-space@github
//
// DESCRIPTION:
//    Implements counting of dynamic function calls.
//
//    This a module pass that:
//     1. Inserts a global variable, lt_RUNTIME_numFunctions, that stores the
//        number of functions in the module:
//          extern uint64_t lt_RUNTIME_numFunctions;
//     2. Inserts a global array of structs, lt_RUNTIME_functionInfo, in which
//        there's one element per each function in the module that contains the
//        number of times each function is called:
//          struct {
//            char *name;
//            uint64_t count;
//          } lt_RUNTIME_functionInfo[];
//     3. Declares the counter function:
//          void lt_RUNTIME_called(uint64_t id)
//     4. Declares the function printing the results of the analysis:
//          void lt_RUNTIME_print()
//        This function will use the contents of lt_RUNTIME_functionInfo. It's
//        installed with other destructor to guarantee that it's executed at
//        the end of the module.
//     5. For each function defined in this module, inserts a call to
//        lt_RUNTIME_called at the beginning of each funciton
//     6. For each call to an externally defined function, inserts a call to
//        lt_RUNTIME_called just before the call site instruction (we can't
//        instrument externally defined functions).
//
// License: MIT
//========================================================================
#include "DynamicCallCounter.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

using namespace llvm;
using lt::DynamicCallCounter;

namespace lt {

char DynamicCallCounter::ID = 0;

}  // namespace lt

// Returns a map (Function* -> uint64_t).
static DenseMap<Function *, uint64_t>
computeFunctionIDs(llvm::ArrayRef<Function *> functions) {
  DenseMap<Function *, uint64_t> idMap;

  size_t nextID = 0;
  for (auto f : functions) {
    idMap[f] = nextID;
    ++nextID;
  }

  return idMap;
}

// Returns a set of all internal (defined) functions.
static DenseSet<Function *>
computeInternal(llvm::ArrayRef<Function *> functions) {
  DenseSet<Function *> internal;

  for (auto f : functions) {
    if (!f->isDeclaration()) {
      internal.insert(f);
    }
  }

  return internal;
}

static llvm::Constant *createConstantString(llvm::Module &m,
                                            llvm::StringRef str) {
  auto &context = m.getContext();

  auto *name = llvm::ConstantDataArray::getString(context, str, true);
  auto *int8Ty = llvm::Type::getInt8Ty(context);
  auto *arrayTy = llvm::ArrayType::get(int8Ty, str.size() + 1);
  auto *asStr = new llvm::GlobalVariable(
      m, arrayTy, true, llvm::GlobalValue::PrivateLinkage, name);

  auto *zero = llvm::ConstantInt::get(llvm::Type::getInt32Ty(context), 0);
  llvm::Value *indices[] = {zero, zero};
  return llvm::ConstantExpr::getInBoundsGetElementPtr(arrayTy, asStr, indices);
}

// Creates the global lt_RUNTIME_functionInfo table used by the runtime library.
static void createGlobalFunctionTable(Module &m, uint64_t numFunctions) {
  auto &context = m.getContext();

  // 1. Create the component types of the table
  auto *int64Ty = Type::getInt64Ty(context);
  auto *stringTy = Type::getInt8PtrTy(context);
  Type *fieldTys[] = {stringTy, int64Ty};
  auto *structTy = StructType::get(context, fieldTys, false);

  // 2. Create and initialize a table of function information
  std::vector<Constant *> functionInfo;
  auto *zero = ConstantInt::get(int64Ty, 0, false);
  std::transform(
      m.begin(), m.end(), std::back_inserter(functionInfo),
      [&m, zero, structTy](auto &f) {
        Constant *structFields[] = {createConstantString(m, f.getName()), zero};
        return ConstantStruct::get(structTy, structFields);
      });

  // 3. Inject the table into the module as a global var
  auto *tableTy = ArrayType::get(structTy, numFunctions);
  auto *functionTable = ConstantArray::get(tableTy, functionInfo);
  new GlobalVariable(m, tableTy, false, GlobalValue::ExternalLinkage,
                     functionTable, "lt_RUNTIME_functionInfo");
}

// For an analysis pass, runOnModule should perform the actual analysis and
// compute the results. The actual output, however, is produced separately.
bool DynamicCallCounter::runOnModule(Module &m) {
  auto &context = m.getContext();

  // 1. Identify the functions we wish to track
  std::vector<Function *> toCount;
  for (auto &f : m) {
    toCount.push_back(&f);
  }

  ids = computeFunctionIDs(toCount);
  internal = computeInternal(toCount);
  auto const numFunctions = toCount.size();

  // 2. Store the number of functions into an externally visible variable.
  auto *int64Ty = Type::getInt64Ty(context);
  auto *numFunctionsGlobal = ConstantInt::get(int64Ty, numFunctions, false);
  new GlobalVariable(m, int64Ty, true, GlobalValue::ExternalLinkage,
                     numFunctionsGlobal, "lt_RUNTIME_numFunctions");

  // 3. Create a global table of function infos
  createGlobalFunctionTable(m, numFunctions);

  // 4. Declare the counter function
  auto *voidTy = Type::getVoidTy(context);
  auto *helperTy = FunctionType::get(voidTy, int64Ty, false);
  auto *counterFunc = m.getOrInsertFunction("lt_RUNTIME_called", helperTy);

  // 5. Declare and install the result printing function so that it prints out
  // the counts after the entire program is finished executing.
  auto *printer = m.getOrInsertFunction("lt_RUNTIME_print", voidTy);
  appendToGlobalDtors(m, llvm::cast<Function>(printer), 0);

  for (auto f : toCount) {
    // We only want to instrument internally defined functions.
    if (f->isDeclaration()) {
      continue;
    }

    // Count each internal function. To this end install a call to
    // lt_RUNTIME_called at the beginning of such function.
    installCCFunction(*f, counterFunc);

    // Count each external function. To this end loop over all instructions in
    // this function and for each function call insert a call to
    // lt_RUNTIME_called just before the call-site instruction.
    for (auto &bb : *f) {
      for (auto &i : bb) {
        installCCInstruction(CallSite(&i), counterFunc);
      }
    }
  }

  return true;
}

void DynamicCallCounter::installCCFunction(Function &f, Value *counter) {
  IRBuilder<> builder(&*f.getEntryBlock().getFirstInsertionPt());
  builder.CreateCall(counter, builder.getInt64(ids[&f]));
}

void DynamicCallCounter::installCCInstruction(CallSite cs, Value *counter) {
  // Check whether the instruction is actually a call
  if (!cs.getInstruction()) {
    return;
  }

  // Check whether the called function is directly invoked
  auto called = dyn_cast<Function>(cs.getCalledValue()->stripPointerCasts());
  if (!called) {
    return;
  }

  // Check if the function is internal or blacklisted.
  if (internal.count(called) || !ids.count(called)) {
    // Internal functions are counted upon the entry of each function body.
    // Blacklisted functions are not counted. Neither should proceed.
    return;
  }

  // External functions are counted at their invocation sites.
  IRBuilder<> builder(cs.getInstruction());
  builder.CreateCall(counter, builder.getInt64(ids[called]));
}
