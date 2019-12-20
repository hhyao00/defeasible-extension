import hhyao_defeasible.py

# example program, knowledge base input
B = 'B'   # belief
D = 'D'   # desire
G = 'G'   # goal
I = 'I'   # intention
SI = 'SI' # social intention
O = 'O'   # obligation
U = 'U'   # outcome

p = '+'
n = '-'

# Given that today is a Saturday and John is sick:
Facts = {Literal(p,U,'saturday'),Literal(p,U,'john_sick')}

# r1 : saturday ⇒OUT visit John * visit parents * watch movie.
# If it is Saturday, then there is the outcome Alice will
# visit John. If she can't visit John then she will visit her
# parents. If she can't visit her parents, she will watch movie.

r1 = Rule(mod = U, antecedent=[Literal(p,U,'saturday')], 
	consequent=[Literal(p,U,'visit_john'),
				Literal(p,U,'visit_parents'),
				Literal(p,U,'watch_movie')],
	superiors=[], inferiors=[])

# r2 : If John is away, then Alice believes she will not visit.

r2 = Rule(mod = B, antecedent=[Literal(p,B,'john_away')],
	consequent=[Literal(n,B,'visit_john')],
	superiors=[], inferiors=[])

# r3 : If John is sick then she will not visit John, however
# if she does visit John, then it will be a short visit.

r3 = Rule(mod = U, antecedent=[Literal(p,U,'john_sick')],
	consequent=[Literal(n,B,'visit_john'),
				Literal(p,B,'short_visit')],
	superiors=[], inferiors = [])

rules = [r1,r2,r3]
DE = DefeasibleExtension(rules)
p_conclusion, n_conclusion = DE.DefeasibleConclusion()
