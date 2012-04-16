#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Argument.h"
#include "llvm/Module.h"
#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/LLVMContext.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <map>

using namespace llvm;

struct ABC3 : public ModulePass 
{
	static char ID; // Pass identification, replacement for typeid
	ABC3() : ModulePass(ID) {}
	
	struct ABCDNode_{
		llvm::Value *value;
		int length; // 0 => not an array length node.
		std::map<struct ABCDNode_* , int> inList;
		std::map<struct ABCDNode_* , int > outList;
		int distance;
		bool isPhi;
		ABCDNode_ *predecessor;
		int name;
		
		bool operator<(const ABCDNode_& x)const{
      if(this->value < x.value) return true;
      return false;
    }
	};
	
	typedef struct ABCDNode_ ABCDNode;
	
  typedef struct{
		std::map<llvm::Value*, ABCDNode* > arrayLengthList;
		std::map<llvm::Value*, ABCDNode* > variableList;
	}ABCDGraph;
	
	//create C and active as global variables
	struct triplet_{
	  ABCDNode a;
	  ABCDNode b;
	  int red;
	  
	  bool operator<(const triplet_& x)const{
      if(this->a < x.a || this->b < x.b || this->red < x.red) return true;
      return false;
    }
  };

	typedef struct triplet_ triplet;
	
	std::map<triplet,int> *C; 
	std::map<ABCDNode,int> *active;
	
  bool demandProve(ABCDGraph G, ABCDNode a, ABCDNode b, int c)
  {
    //initialize C and active
    C = new std::map<triplet,int>();
    active = new std::map<ABCDNode,int>();
    
    if(prove(a,b,c))
    {
      return true;
    }
    return false;
  }
  
  int prove(ABCDNode a, ABCDNode b, int c)
  {
    triplet *t = new triplet();
    t->a = a; t->b = b; t->red = 2;
    std::map<triplet,int>::iterator it = C->find(*t);
    //same or stronger difference was already proven
    if(it != C->end() && c >= it->second) return 2;
    t->red = 0;
    it = C->find(*t);
    //same or weaker difference was already disproved
    if(it != C->end() && c <= it->second) return 0;
    t->red = 1;
    it = C->find(*t);
    //b is on a cycle that was reduced for same or stronger difference
    if(it != C->end() && c >= it->second) return 1;
    //traversal reached the source vertex, success if a-a<=c
    if(b.value == a.value && c >= 0) return 2;
    //if no constraint exists on the value of b, we fail
    if(b.inList.empty()) return 0;
    std::map<ABCDNode,int>::iterator ait = active->find(b);
    //a cycle was encountered
    if(ait != active->end())
    {
      if(c > (*active)[b]) return 0; //an amplifying cycle
      return 1;                 //a "harmless" cycle
    } 
    int ret;
    (*active)[b] = c;
    std::map<struct ABCDNode_* , int>::iterator itt;
    if(b.isPhi)
    {
      ret = 2; 
      for(itt = (b.inList).begin(); itt != b.inList.end(); itt++)
      {
        int res = prove(a,*(*itt).first,c-(*itt).second);
        ret = res < ret ? res : ret;
      }
      if(ret == 0)
      {
        t->red = 0;
        it = C->find(*t);
        if(it == C->end()) (*C)[*t] = c;
        else if(c > it->second) (*C)[*t] = c;
      }
      else if(ret == 1)
      {
        t->red = 0;
        it = C->find(*t);
        if(it == C->end() || (it != C->end() && c < it->second))
        {
          t->red = 1;
          it = C->find(*t);
          if(it == C->end()) (*C)[*t] = c;
          else if(c < it->second) (*C)[*t] = c;
        }
      }
      else if(ret == 2)
      {
        t->red = 0;
        it = C->find(*t);
        if(it == C->end() || (it != C->end() && c < it->second))
        {
          t->red = 1;
          it = C->find(*t);
          if(it == C->end() || (it != C->end() && c > it->second))
          {
            t->red = 2;
            it = C->find(*t);
            if(it == C->end()) (*C)[*t] = c;
            else if(c < it->second) (*C)[*t] = c;
          }
        }
      }
    }
    else
    {
      ret = 0;
      for(itt = b.inList.begin(); itt != b.inList.end(); itt++)
      {
        int res = prove(a,*(*itt).first,c-(*itt).second);
        ret = res > ret ? res : ret;
      }
      if(ret == 2)
      {
        t->red = 2;
        it = C->find(*t);
        if(it == C->end()) (*C)[*t] = c;
        else if(c < it->second) (*C)[*t] = c;
      }
      else if(ret == 1)
      {
        t->red = 2;
        it = C->find(*t);
        if(it == C->end() || (it != C->end() && c > it->second))
        {
          t->red = 1;
          it = C->find(*t);
          if(it == C->end()) (*C)[*t] = c;
          else if(c < it->second) (*C)[*t] = c;
        }
      }
      else if(ret == 0)
      {
        t->red = 2;
        it = C->find(*t);
        if(it == C->end() || (it != C->end() && c > it->second))
        {
          t->red = 1;
          it = C->find(*t);
          if(it == C->end() || (it != C->end() && c > it->second))
          {
            t->red = 0;
            it = C->find(*t);
            if(it == C->end()) (*C)[*t] = c;
            else if(c > it->second) (*C)[*t] = c;
          }
        }
      }
    }
    active->erase(b);
    return ret;
  }

	virtual bool runOnModule(Module &M) {

    return true;
	}
};


char ABC3::ID = 0;
static RegisterPass<ABC3> ABC3("abc3", "auto bounds check");
