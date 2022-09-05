import sys
'''install was with: sudo apt-get install -y python-pygraphviz'''
import networkx as nx
from networkx.drawing.nx_agraph import graphviz_layout
import matplotlib.pyplot as plt
from datetime import datetime
import logging
import re

G = nx.DiGraph()
logging.basicConfig(filename='compile_log.log', level=logging.INFO, format='%(message)s')

def read_FOL(f_name):
	data = open(f_name, 'r')
	ls = data.readlines()
	headers = {}
	for row in ls:
		row_lis = row.split()
		if ":" == row_lis[0][-1]:
			if row_lis[0] == "formula:":
				headers[row_lis[0][:-1]] = split_formula(' '.join(row_lis[1:]))
			else:
				headers[row_lis[0][:-1]] = row_lis[1:] 
		else:
			headers["formula"] += ['\n'] + split_formula(row)
	data.close()	
	return headers

def split_formula(formula):
	formula = ' ) '.join(formula.split(')'))
	formula = ' ( '.join(formula.split('('))
	formula = ' , '.join(formula.split(','))
	formula = formula.split()
	return formula

def validate_input_file(tokens):
	global errors
	headers = {"variables", "constants", "predicates", "equality", "connectives", "quantifiers", "formula"}
	head_dif, formula = headers - set(tokens.keys()), None
	if head_dif:
		errors.append("Error:	Missing set identifier(s) " + ', '.join(head_dif))
	for typ in tokens.keys():
		typ_len = len(tokens[typ])
		if typ in ["variables", "constants"] :
			for term in tokens[typ]:
				if not re.match(r'(\w+)$', term):
					errors.append("Error in " + typ + " set: " + term + " is an invalid " + typ[:-1] + " format")
		elif typ == "predicates":
			for term in tokens[typ]:
				if not re.match(r'(\w+)\[(\d+)\]', term):
					errors.append("Error in " + typ + " set: " + term + " is an invalid " + typ + " format")
		elif typ == "equality":
			if typ_len == 1: 
				if not re.match(r'(\w|\\|=)+$', tokens[typ][0]):
					errors.append("Error in " + typ + " set: " + tokens[typ][0] + " is an invalid " + typ + " format")
			else:
				errors.append("Error in " + typ + " set:	Should contain 1 element, instead contains " + str(typ_len))
		elif typ == "connectives":
			if typ_len == 5: 
				if not re.match(r'(\w|\\)+$', tokens[typ][0]):
					errors.append("Error in " + typ + " set: " + tokens[typ][0] + " is an invalid " + typ + " format")
			else:
				errors.append("Error in " + typ + " set:	Should contain 5 elements, instead contains " + str(typ_len))
		elif typ == "quantifiers":
			if typ_len == 2: 
				if not re.match(r'(\w|\\)+$', tokens[typ][0]):
					errors.append("Error in " + typ + " set: " + tokens[typ][0] + " is an invalid " + typ + " format")
			else:
				errors.append("Error in " + typ + " set:	Should contain 2 elements, instead contains " + typ_len)
		elif typ == "formula":
			formula = tokens[typ]
		else:
			errors.append("Error: " + typ + " is not a valid set identifier")
	if "formula" in tokens.keys():
		del tokens["formula"]
	return formula, tokens	

def lexical_analysis(tokens, formula):
	'''Wantto check that predicates, variables and constants all have different names. Also want to make equality, connectives and quantifiers	'''
	global errors
	token_stream = []
	line, line_lens  = 0, 0
	for pointer, lex in enumerate(formula):
		if lex == '\n':
			line += 1
			line_lens = pointer+1
		elif lex in tokens["variables"]:
			symb_table.append({"lexeme": lex, "line": str(line), "position": str(pointer - line_lens)})
			token_stream.append(["Var", len(symb_table) - 1])
		elif lex in tokens["constants"]:
			symb_table.append({"lexeme": lex, "line": str(line), "position": str(pointer - line_lens)})
			token_stream.append(["Const", len(symb_table) - 1])
		elif lex in tokens["predicates"].keys():
			symb_table.append({"lexeme": lex, "line": str(line), "position": str(pointer - line_lens)})
			token_stream.append(["Pred"+tokens["predicates"][lex], len(symb_table) - 1])
		elif lex in tokens["equality"]:
			symb_table.append({"lexeme": lex, "line": str(line), "position": str(pointer - line_lens)})
			token_stream.append(["Equal", len(symb_table) - 1])
		elif lex in tokens["UCon"]:
			symb_table.append({"lexeme": lex, "line": str(line), "position": str(pointer - line_lens)})
			token_stream.append(["UCon", len(symb_table) - 1])
		elif lex in tokens["connectives"]:
			symb_table.append({"lexeme": lex, "line": str(line), "position": str(pointer - line_lens)})
			token_stream.append(["BCon", len(symb_table) - 1])
		elif lex in tokens["quantifiers"]:
			symb_table.append({"lexeme": lex, "line": str(line), "position": str(pointer - line_lens)})
			token_stream.append(["Quan", len(symb_table) - 1])
		elif lex == "(" or lex == ")" or lex == ",":
			symb_table.append({"lexeme": lex, "line": str(line), "position": str(pointer - line_lens)})
			token_stream.append([lex, len(symb_table) - 1])
		else:
			error = "Error on line " + str(line) + " at position " + str(pointer - line_lens) + ", symbol " + lex + " is not defined in the language give"
			errors.append(error)
	return token_stream

def S(lookahead, remaining, p_num):
	lookahead1, remaining = Form(lookahead, remaining, p_num)
	if lookahead1[0] != " ":
		handle_error(lookahead, lookahead1, " ", remaining)

def Form(lookahead, remaining, p_num):
	'''All checks for closing brackets should be passed the opening bracket token'''
	global solve_err_at, errors
	c_num = push_to_tree(p_num, "Form")
	if not solve_err_at:
		if lookahead[0] == "Quan":
			lookahead1, remaining = match(None, lookahead, "Quan", remaining, c_num)
			lookahead2, remaining = match(lookahead, lookahead1, "Var", remaining, c_num)
			lookahead, remaining = Form(lookahead2, remaining, c_num)
		elif lookahead[0] == "UCon":
			lookahead1, remaining = match(None, lookahead, "UCon", remaining, c_num)
			lookahead, remaining = Form(lookahead1, remaining, c_num)
		elif lookahead[0]  == "(":
			lookahead1, remaining = match(None, lookahead, "(", remaining, c_num)
			lookahead2, remaining = Brack(lookahead1, remaining, c_num)
			lookahead = lookahead if solve_err_at else lookahead1
			lookahead, remaining = match(lookahead, lookahead2, ")", remaining, c_num)
		elif "Pred" in lookahead[0]:
			arity = lookahead[0].replace("Pred", "")
			lookahead3, remaining = match(None, lookahead, "Pred"+arity, remaining, c_num)
			lookahead2, remaining = match(lookahead, lookahead3, "(", remaining, c_num)
			for ari in range(int(arity)-1):
				lookahead3, remaining = match(lookahead3, lookahead2, "Var", remaining, c_num)
				lookahead2, remaining = match(lookahead2, lookahead3, ",", remaining, c_num)
			lookahead4, remaining = match(lookahead3, lookahead2, "Var", remaining, c_num)
			lookahead, remaining = match(lookahead2, lookahead4, ")", remaining, c_num)
		else:
			current_entry = symb_table[lookahead[1]]
			if lookahead[0] == " ":
				current_entry["lexeme"] = "\" \""
			error = "Error on line "+current_entry["line"]+" at position "+current_entry["position"]+", "+current_entry["lexeme"]+" is not a valid starting symbol for a formulae"
			errors.append(error)
			lookahead, remaining = pop_to(lookahead, remaining, 0, 1)
	return lookahead, remaining

def Brack(lookahead, remaining, p_num):
	global solve_err_at, errors
	c_num = push_to_tree(p_num, "Brack")
	if not solve_err_at:
		if lookahead[0] == "Const":
			lookahead1, remaining = match(None, lookahead, "Const", remaining, c_num)
			lookahead2, remaining = match(lookahead, lookahead1, "Equal", remaining, c_num)
			lookahead, remaining = VCon(lookahead2, remaining, c_num)
		elif lookahead[0] == "Var":
			lookahead1, remaining = match(None, lookahead, "Var", remaining, c_num)
			lookahead2, remaining = match(lookahead, lookahead1, "Equal", remaining, c_num)
			lookahead, remaining = VCon(lookahead2, remaining, c_num)
		elif lookahead[0][:4] in ["Quan", "UCon", "(", "Pred"]:
			lookahead1, remaining = Form(lookahead, remaining, c_num)
			lookahead, remaining = match(lookahead, lookahead1, "BCon", remaining, c_num)
			lookahead, remaining = Form(lookahead, remaining, c_num)
		else:
			current_entry = symb_table[lookahead[1]]
			if lookahead[0] == " ":
				current_entry["lexeme"] = "\" \""
			error = "Error on line "+current_entry["line"]+" at position "+current_entry["position"]+", symbol "+current_entry["lexeme"]+" cannot be used following \"(\""
			errors.append(error)
			lookahead, remaining = pop_to(lookahead, remaining, 0, 1)
		return lookahead, remaining

def VCon(lookahead, remaining, p_num):
	global solve_err_at, errors
	c_num = push_to_tree(p_num, "VCon")
	if not solve_err_at:
		if lookahead[0] == "Var":
			lookahead, remaining = match(None, lookahead, "Var", remaining, c_num)
		elif lookahead[0] == "Const":
			lookahead, remaining = match(None, lookahead, "Const", remaining, c_num)
		else:
			current_entry = symb_table[lookahead[1]]
			if lookahead[0] == " ":
				current_entry["lexeme"] = "\" \""
			error = "Error on line "+current_entry["line"]+" at position "+current_entry["position"]+", symbol "+current_entry["lexeme"]+" with type "+lookahead[0]+" cannot be used following equality"
			errors.append(error)
			lookahead, remaining = pop_to(lookahead, remaining, 0, 1)
	return lookahead, remaining

def match(current, lookahead, token, remaining, p_num):
	global solve_err_at
	c_num = push_to_tree(p_num, lookahead[0]) if p_num else False
	if lookahead[0] == token:
		solve_err_at = False
		if lookahead[0] not in ["(", ",", ")"]:
			push_to_tree(c_num, symb_table[lookahead[1]]["lexeme"])
		if remaining:
			lookahead = remaining.pop(0)
		else:
			lookahead = [" ", lookahead[1]]
	elif not solve_err_at:
		lookahead, remaining = handle_error(current, lookahead, token, remaining)
	return lookahead, remaining

def handle_error(current, lookahead, token, remaining):
	global solve_err_at, errors
	current_entry, look_entry = symb_table[current[1]], symb_table[lookahead[1]]
	look_entry["lexeme"] = look_entry["lexeme"] if lookahead[0] else "\" \""
	
	if token == "Var":
		'''Can be after a bracket in a predicate or equality(same outcome), after an equality (same outcome) or after a quantifier
		which should pop until start of a new formulae'''
		error = "Error on line "+look_entry["line"]+" at position "+look_entry["position"]+", missing variable after "+current_entry["lexeme"]

	elif token == "Const":
		'''Can only ever be afer either a bracket or and equality and so is always within brackets, leading to deletion until closing bracket'''
		error = "Error on line "+look_entry["line"]+" at position "+look_entry["position"]+", missing constant after "+current_entry["lexeme"]

	elif token == ")":
		'''Always used to close a predicate or an equality, both of which are formulae. Formulae can only ever be followed by a binary conjunctive. Therefore
		if the next is not a conjunctive either then is reasonable to delete to next bracket and not attempt proper recovery'''
		error = "Error on line "+look_entry["line"]+" at position "+look_entry["position"]+", missing \")\""
		
	elif token == "(":
		error = "Error on line "+look_entry["line"]+" at position "+look_entry["position"]+", missing \"(\" after "+current_entry["lexeme"]

	elif token == ",":
		''' , can only follow variables in predicate, therefore, if following is not a variable then multiple errors and should remove to closing bracket'''
		error = "Error on line "+look_entry["line"]+" at position "+look_entry["position"]+", "+current_entry["lexeme"]+" must be followed by a comma"
	elif token == "Equal":
		'''Equality can only ever be followed by a variable or a constant, therefore, if following is neither then can remove to closing bracket'''
		error = "Error on line "+look_entry["line"]+" at position "+look_entry["position"]+", "+current_entry["lexeme"]+" must be followed by the equality symbol here"
	elif token == "BCon":
		'''Can only ever occur between two formulae so if next symbol isn't a starting symbol for valid formulae then should delete to bracket'''
		error = "Error on line "+look_entry["line"]+" at position "+look_entry["position"]+", formulae can only be followed by a binary conjunctive not "+ look_entry["lexeme"]

	elif token == " ":
		error = "Error on line "+look_entry["line"]+" at position "+look_entry["position"]+", symbols present after closing of first bracket pair, this would suggest a missing openening bracket"

	lookahead, remaining = pop_to(lookahead, remaining, 0, 1)
	errors.append(error)
	return lookahead, remaining

def pop_to(lookahead, remaining, no_c, no_o):
	global solve_err_at, errors
	start, current = True, lookahead
	while no_o != no_c and remaining:
		if not start:
			lookahead = remaining.pop(0)
		if lookahead[0] == "(":
			no_o += 1
		elif lookahead[0] == ")":
			no_c += 1
		start = False
	if no_o != no_c:
		solve_err_at = " "
		return [" ", " "], remaining
	solve_err_at = ")"
	return lookahead, remaining

def push_to_tree(p_num, node):
	global node_num
	node_num += 1
	G.add_node(node_num, label=node)
	labels[node_num] = node
	if p_num > 1:
		G.add_edge(p_num, node_num)
	return node_num	

def log(in_name):
		global errors
		
		time = datetime.now().strftime("%d %b %H:%M")
		validity = "Valid" if not errors else "Invalid"
		first_msg = "The file provided is of the correct format and the formula is valid" if not errors else errors.pop(0)
		logging.info(in_name + '	' + time + '	' + validity + '		' + first_msg)
		time_size = len(time) * " "
		in_name_size = len(in_name) * " "
		for err in errors:
			logging.info(in_name_size + '	' + time_size + '	' + validity + '		' + err)
			
		logging.info(" ")

def show_grammar(tokens, file_name):
	all_lines = []

	T = list(tokens["predicates"].keys())
	pred_arities, pred_brac = [], []
	for lex in tokens["predicates"].keys():
		pred = "Pred"+tokens["predicates"][lex]
		brac = " ( "+" , ".join(["Var" for i in range(int(pred[4:]))])+" )"
		pred_arities.append(pred)
		pred_brac.append(pred+brac)
	N = "Form Var Brack VarConst Const BCon UCon Equal Quan " + " ".join(pred_arities)
	for tok in tokens.keys():
		if tok != "predicates":
			T += tokens[tok]
	all_lines.append("For the language given, the corresponding grammar of valid FO formula is given by\n")
	all_lines.append("	G = {\n		T = {" + " ".join(T) + " ( ) ,}, \n		N = {" + N + "}, \n		P, \n		Form\n	}\n")
	all_lines.append("Where P includes:\n")
	all_lines.append("		Form -> " + "Quan Var Form | UCon Form | ( Brack ) | " + " | ".join(pred_brac) + "\n")
	all_lines.append("		VCon -> " + "Var | Const" + "\n")
	all_lines.append("		Var -> " + " | ".join(tokens["variables"]) + "\n")
	all_lines.append("		Brack -> " + "Const Equal VCon | Var Equal VCon | Form BCon Form" + "\n")
	all_lines.append("		Const -> " + " | ".join(tokens["constants"]) + "\n")
	all_lines.append("		UCon -> " + " | ".join(tokens["UCon"]) + "\n")
	all_lines.append("		BCon -> " + " | ".join(tokens["connectives"]) + "\n")
	all_lines.append("		Equal -> " + " | ".join(tokens["equality"]) + "\n")
	all_lines.append("		Quan -> " + " | ".join(tokens["quantifiers"]) + "\n")
	for pred in pred_arities:
		pred_l = [] 
		for val in tokens["predicates"].keys():
			if tokens["predicates"][val] == pred[4:]:
				pred_l.append(val)
		all_lines.append("		" + pred + " -> " + repr(" | ".join(pred_l))[1:-1] + "\n")
	all_lines.append("\n\n")

	file_o = open(file_name, "w")
	file_o.writelines(all_lines)
	file_o.close()
	
def main():
	file_name = sys.argv[1][:-4]
	tokens = read_FOL(file_name+".txt")
	formula, tokens = validate_input_file(tokens)
	if not errors:
		tokens["UCon"] = [tokens["connectives"].pop()]
		tokens["predicates"] = {pred[:pred.index('[')]: pred[pred.index('[')+1:-1] for pred in tokens["predicates"]}
		show_grammar(tokens, file_name + "_grammar.txt")
		token_stream = lexical_analysis(tokens, formula) 
		if token_stream:
			S(token_stream[0], token_stream[1:], 1)
			if not errors:
				print("Formula is valid")
				pos = graphviz_layout(G, prog='dot')
				plt.figure(1, figsize=(12,12))
				nx.draw(G, pos, labels=labels, font_size=10, node_size=800, with_labels=True)
				plt.savefig(file_name+".png")
			else:
				print("Formula is invalid")	
	log(file_name+".txt")

node_num, labels = 1, {}
symb_table, solve_err_at = [], False
errors = []
main()
