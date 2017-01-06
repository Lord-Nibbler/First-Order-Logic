##########################
##
##  H O M E W O R K - 3
##
##########################

import sys
import ply.lex as lex
import ply.yacc as yacc

class parser:
	tokens = ['NAME', 'COMMA', 'LPARAN', 'RPARAN', 'NOT', 'OPER']

	t_ignore = ' \t'

	def t_NAME(self, t):
		r'[a-zA-Z0-9_]+'
		return t

	def t_COMMA(self, t):
		r','
		return t

	def t_LPARAN(self, t):
		r'\('
		return t

	def t_RPARAN(self, t):
		r'\)'
		return t	

	def t_NOT(self, t):
		r'\~'
		return t

	def t_OPER(self, t):
		r'\| | \& | \^ | =>'
		return t

	def p_sentence(self, p):
		'''sentence : LPARAN sentence RPARAN 
					| clause'''
		if len(p) == 4:
			p[0] = p[2]
		elif len(p) == 2: # only for a clause
			p[0] = p[1]

	def p_clause(self, p):
		'''clause : sentence OPER sentence
			      | literal'''
		if len(p) == 4:
			oper = p[2]
			if oper == '&' or oper == '^':
				p[0] = ('and', p[1], p[3])
			elif oper == '|':
				p[0] = ('or', p[1], p[3])
			elif oper == '=>':
				p[0] = ('=>', p[1], p[3])
				
		elif len(p) == 2:
			p[0] = p[1]

	def p_literal(self, p):
		'''literal : LPARAN NOT sentence RPARAN
				   | term'''
		if len(p) == 5:
			p[0] = ('not', p[3])
		elif len(p) == 2:
			p[0] = p[1]		
		
	def p_term(self, p):
		'''term : NAME LPARAN args RPARAN
				| NAME'''
		if len(p) == 5:
			p[0] = (p[1], ) + p[3]
		elif len(p) == 2:
			p[0] = (p[1], )

	def p_args(self, p):
		'''args : NAME COMMA args
				| NAME'''
		if len(p) == 4:
			p[0] = (p[1], ) + p[3]
		elif len(p) == 2:
			p[0] = (p[1], )
			
	def parse_query(self, query):
		if query[0] == '~':
			return ('not', ) + (self.parse(query[1:]), )
		else:
			return self.parse(query)
	
	def build(self):
		self.lexer = lex.lex(module=self)
		self.yacc = yacc.yacc(module=self)
	
	def test(self, data):
		pass
		'''
		self.lexer.input(data)	

		while True:
			token = self.lexer.token()
			if not token:
				break
			else:
				print(token)
		'''
	
	def parse(self, data):
		return self.yacc.parse(data)
	
	def process(self):
		
		self.build()
		
		queries = list()
		sentences = list()
		file_data = list() 
		
		fname = 'input.txt'
		
		if len(sys.argv) == 2:
			fname = sys.argv[1]	
		
		with open(fname, 'r') as fp:
			file_data = [line for line in (fp.read().splitlines()) if line]
		
		nqueries = int(file_data[0])
		for query in file_data[1:nqueries+1]:
			queries.append(self.parse_query(query))
		
		nsentences = int(file_data[nqueries+1])
		for sentence in file_data[nqueries+2:nqueries+nsentences+3]:
			sentences.append(self.parse(sentence))
		
		return (queries, sentences)
		

# Collection of utility functions			
class utils:
	
	def __init__(self):
		self.rec_ctr = 0
		self.rec_threshold = 500
		pass
	
	def reset_ctr(self):
		self.rec_ctr = 0
		
	def is_operator(self, expr, operator):
		if isinstance(expr, tuple):
			if expr[0] == operator:
				return True
		return False		
	
	def is_variable(self, expr):
		if isinstance(expr, str):
			if len(expr) and expr[0] == expr[0].lower():
				return True
		return False

	def is_constant(self, expr):
		if isinstance(expr, str):
			if len(expr) and expr[0] == expr[0].upper():
				return True
		return False
	
	def is_predicate(self, expr):
		if isinstance(expr, tuple):
			if self.is_constant(expr[0]):
				return True
		return False		
			
	def map_args(self, operator, function, expression):
		return (operator,) + tuple([function(x) for x in expression[1:]])
	
	def get_size(self, tup):
		if isinstance(tup, tuple):
			size = 0
			for t in tup:
				size += self.get_size(t)
			return size
		else:
			return 1
	
	def add_suffix(self, variable, suffix):
		uscridx = variable.rfind("_") # get the last occurance of underscore
		if uscridx == -1:
			return variable + "_" + suffix
		else:
			return variable[0:uscridx] + "_" + suffix
 	
	def conjuncts(self, expr):
		if self.is_operator(expr, 'and'):
			return expr[1:]
		else:
			ret_val = list()
			ret_val.append(expr)
			return ret_val
	
	def get_predicate(self, expr):
		if isinstance(expr, tuple):
			if expr[0] == 'not':
				expr = expr[1]
			if isinstance(expr, tuple):
				if expr[0][0].isupper():
					return expr[0]
		else:
			pass
			# TODO: Raise an exception here
			
	def get_disjunct_set(self, expr):
		if self.is_operator(expr, 'or'):
			return set(expr[1:])
		else:
			ret_val = list()
			ret_val.append(expr)
			return set(ret_val)
	
	def eliminate_implications(self, expr):
		if isinstance(expr, tuple):
			operator = expr[0]
			if operator == '=>':
				antecedent = expr[1]
				consequent = expr[2]
				return ('or', self.eliminate_implications(('not', antecedent)), self.eliminate_implications(consequent))
			else:
				return self.map_args(operator, self.eliminate_implications, expr)
				
		else:
			return expr
	
	def move_not_inwards(self, expr):
		if isinstance(expr, tuple):
			oper = expr[0]
			if oper == 'not':
				expr = expr[1]
				if isinstance(expr, tuple):
					oper = expr[0]
					if oper == 'not':
						expr = expr[1]
						return self.move_not_inwards(expr)
					elif oper == 'or':
						lhs = expr[1]
						rhs = expr[2]
						return ('and', self.move_not_inwards(('not', lhs)), self.move_not_inwards(('not', rhs)))
					elif oper == 'and':
						lhs = expr[1]
						rhs = expr[2]
						return ('or', self.move_not_inwards(('not', lhs)), self.move_not_inwards(('not', rhs)))
					else:
						return ('not', self.map_args(oper, self.move_not_inwards, expr))
				else:
					return ('not', expr)
			else:
				return self.map_args(oper, self.move_not_inwards, expr)
		else:
			return expr
	
	def distribute_and_over_or(self, expr):
		if self.is_operator(expr, 'or'):
			temp, lhs, rhs = expr
			lhs, rhs = self.distribute_and_over_or(lhs), self.distribute_and_over_or(rhs)
			
			if self.is_operator(lhs, 'and'):
				t, l, r = lhs
				return ('and', self.distribute_and_over_or(('or', l, rhs)), self.distribute_and_over_or(('or', r, rhs)))
			elif self.is_operator(rhs, 'and'):
				t, l, r = rhs
				return ('and', self.distribute_and_over_or(('or', l, lhs)), self.distribute_and_over_or(('or', r, lhs)))
			else:
				return ('or', lhs, rhs)
		elif isinstance(expr, tuple):
			return self.map_args(expr[0], self.distribute_and_over_or, expr)
		else:
			return expr
	
	def simplify(self, expr):
		if isinstance(expr, tuple):
			if expr[0] == 'and' or expr[0] == 'or':
				oper, lhs, rhs = expr
				lhs = self.simplify(lhs)
				rhs = self.simplify(rhs)
				if self.is_operator(lhs, oper):
					ret_val = lhs[1:]
				else:
					ret_val = (lhs, )
				if self.is_operator(rhs, oper):
					ret_val += rhs[1:]
				else:
					ret_val += (rhs, )
				return (oper, ) + ret_val
			else:
				return self.map_args(expr[0], self.simplify, expr)
		else:
			return expr
	
	def convert_to_cnf(self, expr):
		expr = self.eliminate_implications(expr)
		expr = self.move_not_inwards(expr)
		expr = self.distribute_and_over_or(expr)
		expr = self.simplify(expr)
		return expr
	
	def occurs_check(self, x, y):
		if self.is_variable(y):
			if x == y:
				raise UnificationError()
		elif isinstance(y, tuple):
			for i in y[1:]:
				self.occurs_check(x, i)
				
	def unify_var(self, x, y, d):
		if x in d:
			return self.unify(d[x], y, d)
		else:
			self.occurs_check(x, y)
			d[x] = y
			return d
	
	def unify_sequence(self, x, y, d):
		if len(x) != len(y):
			raise UnificationError()
		else:
			for i in range(len(x)):
				d = self.unify(x[i], y[i], d)
			return d	
			
	def unify(self, x, y, d):
		if isinstance(x, int) and isinstance(y, int) and x == y:
			return d
		elif self.is_constant(x) and self.is_constant(y) and x == y:
			return d
		elif self.is_variable(x):
			return self.unify_var(x, y, d)
		elif self.is_variable(y):
			return self.unify_var(y, x, d)
		elif self.is_predicate(x) and self.is_predicate(y):
			if x[0] != y[0]:
				raise UnificationError()
			else:
				return self.unify_sequence(x[1:], y[1:], d)
		elif isinstance(x, list) and isinstance(y, list):
			return self.unify_sequence(x, y)
		else:
			raise UnificationError()
			
	def apply_substitution(self, x, d):
		if self.is_variable(x):
			while x in d:
				x = d[x]
			return x
		elif isinstance(x, tuple):
			return (x[0], ) + tuple([self.apply_substitution(i, d) for i in x[1:]])
		return x
	
	def resolve(self, clauses, query, substitutions, h=0):
		
		if self.rec_ctr > self.rec_threshold:
			raise InfiniteRecursionError
		
		self.rec_ctr += 1
		
		# Sort the clauses to begin with
		clauses.sort(key = lambda x: x.get_len())
		for clause in clauses:
			clause = clause.standardize_apart(str(h+1))
			r = clause.resolve(query)
			if r is not False:
				sub, k  = r
				if len(k) == 0:
					raise Solved
				else:
					if sub:
						k = k.apply_substitution(sub)
						if k in clauses:
							continue
					self.resolve(clauses + [query], k, (sub, substitutions), h+1)
	
	def print_solution(self):
		pass
		
	def write_output(self, output_list):
		fname = 'output.txt'
		with open(fname, 'w') as fp:
			fp.write('\n'.join([str(x).upper() for x in output_list]))
		
class UnificationError(Exception):
	pass
	
# Representation of a clause
class clause:
	
	def __init__(self, literals):
		self.utils = utils()
		self.predicates = dict()
		self.literals = set(literals)
		for literal in literals:
			predicate = self.utils.get_predicate(literal)
			if  predicate in self.predicates:
				self.predicates[predicate].append(literal)
			else:
				self.predicates[predicate] = list()
				self.predicates[predicate].append(literal)
	
	def __eq__(self, other):
		if isinstance(other, clause):
			if self.literals == other.literals:
				return True
		return False
	
	def __len__(self):
		return len(self.literals)
	
	'''
	def print_clause(self):
		#pass
		print(self.literals)
		print()
		print(self.predicates)
		print("--------------------------------------------")
	'''
	def apply_substitution(self, d):
		return clause(set([self.utils.apply_substitution(x, d) for x in self.literals]))
	
	def get_len(self):
		l = 0
		for lit in self.literals:
			l += self.utils.get_size(lit)
		return l	
	
	def standardize(self, expr, h, d):
		if isinstance(expr, tuple):
			return (expr[0],) + tuple([self.standardize(x, h, d) for x in expr[1:]])
			
		elif self.utils.is_variable(expr):
			if expr in d.keys():
				return d[expr]
			else:
				d[expr] = self.utils.add_suffix(expr, h)
				return d[expr]
		
		else:
			return expr
		
	# Remove overlap of variables!
	def standardize_apart(self, suffix):
		ret_val = list()
		d = dict()
		for l in self.literals:
			ret_val.append(self.standardize(l, suffix, d))
		
		ret_val = set(ret_val)
		return clause(ret_val)
	
	def get_complements(self, c):
		if isinstance(c, clause):
			p = self.predicates
			cp = c.predicates
			if len(p) > len(cp):
				p, cp = cp, p
			s = set()
			ret_val = list()
			for k in p.keys():
				if k in cp:
					for l1 in p[k]:
						for l2 in cp[k]:
							if self.utils.is_operator(l1, 'not') != self.utils.is_operator(l2, 'not'):
								if l1 not in s: 
									if l2 not in s:
										ret_val.append(tuple([l1, l2]))
								s.add(l1)
								s.add(l2)
			return ret_val
			
	def resolve(self, c):
		com = self.get_complements(c)
		if len(com) > 0:
			elim = set()
			for i, j in com:
				if self.utils.is_operator(i, 'not'):
					ii, jj = i[1], j
				else:
					ii, jj = i, j[1]
				try:
					d = dict()
					self.utils.unify(ii, jj, d) # To implement! DONE
				except UnificationError:
					#pass
					return False
				else:
					elim.add(i)
					elim.add(j)
					#print("Eliminated: ",i," ",j)
			
			if len(elim):
				m = clause(self.literals.union(c.literals) - elim)
				return d, m
		return False	

class InfiniteRecursionError(Exception):
	pass
	
class Solved(Exception):
	pass
			
# Representation of the Knowledge Base
class knowledge_base:
	
	def __init__(self):
		self.clauses = list()
		self.utils = utils()
		
	def tell(self, sentence):
		for s in self.utils.conjuncts(self.utils.convert_to_cnf(sentence)):
			self.clauses.append(clause(self.utils.get_disjunct_set(s)))
	
	def ask(self, query):
		
		# Counter to terminate infinite recursion 
		# Dirty Hack. Googled a bit. Seems like this is the only way to solve this problem...
		self.utils.reset_ctr() 
		
		# TODO: Handle negated goals here! DONE
		negate_query = True
		if query[0] == 'not':
			negate_query = False
			query = query[1]
		
		goal = self.utils.conjuncts(self.utils.convert_to_cnf(query))
		
		if not negate_query:
			goal = clause(self.utils.get_disjunct_set(goal[0]))
		else:
			goal = clause([('not', goal[0])])
			
		try:
			self.utils.resolve(self.clauses, goal, None)
		except Solved:
			print("True")
			return True
		except InfiniteRecursionError:
			print("False")
			return False
		except RecursionError:
			print("False")
			return False	
		except Exception:
			print("False")
			return False
		else:
			print("False")
			return False
	
	def print_kb(self):
		for c in self.clauses:
			c.print_clause()
		
if __name__ == "__main__":

	p = parser()
	query, l = p.process()
	u = utils()
	kb = knowledge_base()
	for s in l:
		kb.tell(s)
		
	op_vals = list()
	
	for q in query:
		ret = kb.ask(q)
		op_vals.append(ret)

	u.write_output(op_vals)