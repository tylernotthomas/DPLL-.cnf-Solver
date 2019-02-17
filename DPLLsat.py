#!/usr/bin/python3

import sys, getopt

class SatInstance:
    def __init__(self):
        pass
    def from_file(self, inputfile):
        self.clauses = list()
        self.VARS = set()
        self.model = list()
        self.p = 0
        self.cnf = 0
        with open(inputfile, "r") as input_file:
            self.clauses.append(list())
            maxvar = 0
            for line in input_file:
                tokens = line.split()
                if len(tokens) != 0 and tokens[0] not in ("p", "c"):
                    for tok in tokens:
                        lit = int(tok)
                        maxvar = max(maxvar, abs(lit))
                        if lit == 0:
                            self.clauses.append(list())
                        else:
                            self.clauses[-1].append(lit)
                if tokens[0] == "p":
                    self.p = int(tokens[2])
                    self.cnf = int(tokens[3])
            assert len(self.clauses[-1]) == 0
            self.clauses.pop()
            if not (maxvar == self.p):
                print("Non-standard CNF encoding!")
                sys.exit(5)
      # Variables are numbered from 1 to p
        for i in range(1,self.p+1):
            self.VARS.add(i)
    def __str__(self):
        s = ""
        for clause in self.clauses:
            s += str(clause)
            s += "\n"
        return s



def main(argv):
   inputfile = ''
   verbosity=False
   inputflag=False
   try:
      opts, args = getopt.getopt(argv,"hi:v",["ifile="])
   except getopt.GetoptError:
      print ('DPLLsat.py -i <inputCNFfile> [-v] ')
      sys.exit(2)
   for opt, arg in opts:
       if opt == '-h':
           print ('DPLLsat.py -i <inputCNFfile> [-v]')
           sys.exit()
    ##-v sets the verbosity of informational output
    ## (set to true for output veriable assignments, defaults to false)
       elif opt == '-v':
           verbosity = True
       elif opt in ("-i", "--ifile"):
           inputfile = arg
           inputflag = True
   if inputflag:
       instance = SatInstance()
       instance.from_file(inputfile)
       solve_dpll(instance, verbosity)
   else:
       print("You must have an input file!")
       print ('DPLLsat.py -i <inputCNFfile> [-v]')



def propagate_units(model, symbols, instance):
  #CHECK/FIND UNSATISFIED UNIT CLAUSES
  unitClauses = []
  for i in instance.clauses:
    if len(i) == 1 and abs(i[0]) in symbols:
      #we want to store the number not the list
      unitClauses.append(i[0])

  #UPDATE MODEL:
  for i in unitClauses:
    if i not in model:
      model.append(i)

  #OPERATE ON UNSATISFIED UNIT CLAUSES IF THEY EXIST 
  if unitClauses != []:
    updatedClauses = []
    #we must do this to create a true copy rather than a reference
    updatedClauses.extend(instance.clauses)

    #if a literal is the same sign as the unit clause, delete the clause
    for i in instance.clauses:
      for j in i:
        if j in unitClauses and len(i) != 1:
          updatedClauses.remove(i)
          break

    #if a literal is the opposite sign to the unit clause, remove the literal from the clause
    for i in range(0, len(updatedClauses)):
      for j in updatedClauses[i]:
        if -j in unitClauses:
          updatedClauses[i].remove(j)
          continue
    instance.clauses = updatedClauses

    #REMOVE SATISFIED UNIT CLAUSES FROM SYMBOLS:
    for i in unitClauses:
      if abs(i) in symbols:
        symbols.remove(abs(i))
    #solve_dpll(instance, verbosity)



def pure_elim(model, symbols, instance):
  #FIND PURE LITERALS
  pureLiterals = []
  for i in symbols:
    #note that symbols only contains the positive versions of literals, hence, the counter names are appropriate
    posSignCount = 0
    negSignCount = 0
    for j in instance.clauses:
      if i in j:
        posSignCount = posSignCount + 1
      if -i in j:
        negSignCount = negSignCount + 1
    if (posSignCount > 0 and negSignCount == 0):
      pureLiterals.append(i)
    elif (posSignCount == 0 and negSignCount > 0):
      pureLiterals.append(-i)

  if pureLiterals != []:
    #REMOVE CLAUSES WITH PURE LITERALS
    updatedClauses = []
    #we must do this to create a true copy rather than a reference
    updatedClauses.extend(instance.clauses)
    for i in instance.clauses:
      for j in i:
        if j in pureLiterals:
          updatedClauses.remove(i)
          break

    instance.clauses = updatedClauses

    #UPDATE MODEL AND REMOVE PURE LITERALS FROM SYMBOLS:
    for i in pureLiterals:
      instance.clauses.append([i])
      if i not in model:
        model.append(i)
      if abs(i) in symbols:
        symbols.remove(abs(i))
    #solve_dpll(instance, verbosity)



def check_SAT(model, instance):
  results = []
  for i in range(0, len(instance.clauses)):
    results.append(False)
  
  for i in range(0, len(instance.clauses)):
    for j in instance.clauses[i]:
      if j in model:
        results[i] = True
        break

  if False in results:
    return False
  else:
    return True



def solve(model, VARS, symbols, instance):
  #FOR RECURSION TO WORK:
  #must create a local instance of model list and symbol set
  localModel = []
  for i in model:
    localModel.append(i)

  localSymbols = set()
  for i in symbols:
    localSymbols.add(i)

  propagate_units(model, symbols, instance)
  pure_elim(model, symbols, instance)

  #CHECK IF EMPTY SET IN MODEL
  if [] in localModel:
    return []

  #CHECK IF MODEL CONTAINS ALL VARIABLES
  involveFlag = True
  for i in VARS:
    if (i not in localModel) and (-i not in localModel):
      involveFlag = False

  #IF MODEL CONTAINS ALL VARIABLES...
  if involveFlag:
    #CHECK IF TRUE
    if check_SAT(localModel, instance):
      return localModel

  #PICK A VARIABLE
  if len(localSymbols) != 0:
    x = localSymbols.pop()
  else:
    x = []

  #RECUR
  localModel.append(x)
  if solve(localModel, VARS, localSymbols, instance) != []:
    return solve(localModel, VARS, localSymbols, instance)
  elif x != []:
    localModel.remove(x)
    localModel.append(-x)
    return solve(localModel, VARS, localSymbols, instance)
  else:
    return solve(localModel, VARS, localSymbols, instance)

  



""" Question 2 """
# Finds a satisfying assignment to a SAT instance,
# using the DPLL algorithm.
# Input: a SAT instance and verbosity flag
# Output: print "UNSAT" or
#    "SAT"
#    list of true literals (if verbosity == True)
#    list of false literals (if verbosity == True)
#
#  You will need to define your own
#  solve(VARS, F), pure-elim(F), propagate-units(F), and
#  any other auxiliary functions
def solve_dpll(instance, verbosity):
    # print(instance)
    # print(instance.VARS)
    # print(verbosity)
    ###########################################
    # Start your code
    
    #VARS is a record of all literals that need an assignment
    VARS = set()
    symbols = set()
    for i in instance.VARS:
      VARS.add(i)
      symbols.add(i)

    model = []

    res = solve(model, VARS, symbols, instance)

    #OUTPUT LOGIC
    if res == []:
      print("UNSAT")
    elif verbosity == True:
      print("SAT")
      trueList = []
      falseList = []
      for i in res:
        if i > 0:
          trueList.append(i)
        else:
          falseList.append(i)
      trueList.sort()
      falseList.sort()
      for i in trueList:
        print(i, end = " ")
      print("")
      for i in falseList:
        print(i, end = " ")
      print("")
    else:
      print("SAT")

    # End your code
    return True
    ###########################################


if __name__ == "__main__":
   main(sys.argv[1:])
