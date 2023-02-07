from propositional_logic import *

# replace v by e in all disjuncts
# and return resulting list of clauses
def replaceInAllDisjuncts(disjuncts, v, e):
	"""My original implementation using list comprehension:
	"""
	# replaced_list = [d.replace1(v, e) for d in disjuncts]
	# simplified_replace = [r.simplify() for r in replaced_list]

	"""My perferred implementation using the map function:
	"""
	replaced_list = list(map(lambda d: d.replace1(v, e), disjuncts))
	simplified_replace = list(map(lambda r: r.simplify(), replaced_list))

	return simplified_replace

# replace v by e in all clauses 
# and return resulting list of clauses
def replaceInAllClauses(clauses, v, e):
	# replacedAll_list = list(map(lambda c: replaceInAllDisjuncts(c, v, e), clauses))

	replacedAll_list = [replaceInAllDisjuncts(c, v, e) for c in clauses]
	
	return replacedAll_list

# check if all disjuncts are unsat
# and return True or False
def allDisjunctsUNSAT(disjuncts):

	for d in disjuncts:
		unSAT_BoolConst = d.simplify() == BoolConst(True)
		unSAT_BoolVar = isinstance(d.simplify(), BoolVar)
		unSAT_Not = isinstance(d.simplify(), Not)
		if unSAT_BoolConst or unSAT_BoolVar or unSAT_Not:
			return False

	return True

# check if clauses contains an UNSAT clause
# and return True or False
def containsUNSATClause(clauses):
	
	unSAT_clause_list = [allDisjunctsUNSAT(disjuncts) for disjuncts in clauses]

	return True in unSAT_clause_list

# check if disjuncts has some satisfied disjunct
# and return True or False
def someDisjunctSatisfied(disjuncts):

	for d in disjuncts:
		if d.simplify() == BoolConst(True):
			return True

	return False

# check if all clauses are satisfied
# and return True or False
def allClausesSatisfied(clauses):
	
	clauses_SAT_list = [someDisjunctSatisfied(disjuncts) for disjuncts in clauses]

	return not False in clauses_SAT_list

# the main dpll_sat funcion
# nothing to do here, it just calls the helper dpll
def dpll_sat(f):
	varlist = f.getVars()
	clauses = f.cnfListForm()
	return dpll(clauses, varlist)

def dpll(clauses, varlist):
	if containsUNSATClause(clauses):
		return False
	elif allClausesSatisfied(clauses):
		return True
	else:
		branchVar = varlist[0]
		trueClauses = replaceInAllClauses(clauses, branchVar, BoolConst(True))
		falseClauses = replaceInAllClauses(clauses, branchVar, BoolConst(False))
		return dpll(trueClauses, varlist[1:]) or dpll(falseClauses, varlist[1:])

# the main dpll_model_count funcion
# nothing to do here, it just calls the helper dpll_count
def dpll_model_count(f):
	varlist = f.getVars()
	clauses = f.cnfListForm()
	return dpll_count(clauses, varlist, len(varlist))

def dpll_count(clauses, varlist, t):
	if containsUNSATClause(clauses):
		return 0
	elif allClausesSatisfied(clauses):
		return 2^t
	else:
		branchVar = varlist[0]
		trueClauses = replaceInAllClauses(clauses, branchVar, BoolConst(True))
		falseClauses = replaceInAllClauses(clauses, branchVar, BoolConst(False))
		return dpll_count(trueClauses, varlist[1:], t - 1) + dpll_count(falseClauses, varlist[1:], t - 1)

def equiv_dpll(f1, f2):

	return dpll_sat(f1) == dpll_sat(f2)