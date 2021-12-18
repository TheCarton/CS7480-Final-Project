import lark.visitors
from lark import Lark, Tree, Token
from lark.visitors import Interpreter, visit_children_decor, Transformer
import sys

simppl_parser = Lark(r"""

   e: NAME
      | and
      | or
      | not
      | "true" -> true
      | "false" -> false

   and: "(" "&&" e e ")"
   or: "(" "||" e e ")"
   not: "(" "!" e ")"


   s: assgn
     | flip
     | observe
     | ite
     | seq
     | do

  assgn: NAME "=" e
  flip: NAME "~" "flip" SIGNED_NUMBER
  observe: "observe" s
  seq: s ";" s
  ite: "if" e "{" s "}" "else" "{" s "}"
  do: "do" "{" s "}" "with" "{" s "}"


  p: s ";" "return" e


     %import common.SIGNED_NUMBER
     %import common.WS
     %import common.CNAME -> NAME
     %ignore WS

""", start='p')

"""
###################### Inference Stuff ######################
"""


def exact_prob(tree):
    """Main handling function. Checks for do-operators and handles them, then calls EnumerateSimPPL."""
    observe_tree = tree.find_data("observe")
    for node in observe_tree:
        observed_do_tree = tree.find_data("do")
        for item in observed_do_tree:
            old_tree = item.children[0]
            old_tree_data = old_tree.children[0].data
            new_tree = item.children[1]
            new_tree_data = new_tree.children[0].data
            # item has the two trees I want
            if old_tree_data == "flip":
                tree = DoFlip(old_tree, new_tree).transform(tree)
            elif old_tree_data == "assgn":
                tree = DoAssgn(old_tree, new_tree).transform(tree)

            tree = NoDo().transform(tree)

            tree = NoDo().transform(tree)
    do_tree = tree.find_data("do")
    for item in do_tree:
        raise TypeError("Do operator must be in observe statement.")
    return EnumerateSimPPL(tree).enumerate()


class EnumerateSimPPL(Interpreter):
    """Exact inference method. Recurse down the tree and compute exact probability of return statement
       evaluating to true."""

    def __init__(self, tree, my_vars={}, pr=1, traces=[]):
        self.tree = tree
        self.vars = my_vars
        self.traces = traces
        self.pr = pr
        self.reject = False
        self.visit(tree)

    def enumerate(self):
        numerator = 0
        denom = 0
        for trace in self.traces:
            return_statement = trace[2]
            if return_statement:
                numerator += trace[1]
            denom += trace[1]
        # add up the traces if they are in the return statement
        return numerator / denom

    @visit_children_decor
    def p(self, args):
        return_statement = args[1]
        if not self.reject:
            self.traces.append((self.vars, self.pr, return_statement))

    def s(self, args):
        child_list = args.children
        for child in child_list:
            self.visit(child)

    def seq(self, args):
        child_list = args.children
        for child in child_list:
            self.visit(child)

    def assgn(self, args):
        var_name = args.children[0].value
        var_str = args.children[1].children[0].value
        if var_str == 'true':
            b = True
        else:
            b = False
        self.vars.update({var_name: b})

    def flip(self, args):
        var_name = args.children[0].value
        pr = float(args.children[1].value)
        self.branch(var_name, pr)

    def branch(self, new_var, pr):

        # create new branch for new_var = false
        f_vars = self.vars.copy()
        f_vars.update({new_var: False})
        f_tree = NoFlip(new_var, 'false').transform(self.tree)
        f_pr = self.pr * (1 - pr)
        EnumerateSimPPL(f_tree, f_vars, f_pr)

        # continue on current branch for new_var = true
        self.tree = NoFlip(new_var, 'true').transform(self.tree)
        self.vars.update({new_var: True})
        self.pr = self.pr * pr

    def ite(self, args):
        guard = self.visit(args.children[0])
        if guard:
            self.visit(args.children[1])
        else:
            self.visit(args.children[2])

    def observe(self, args):
        for child in args.children:
            if hasattr(child.children[0], 'data'):
                self.reject = not self.visit(args.children[0])

    def e(self, args):
        child_list = args.children
        for child in child_list:
            if hasattr(child, 'data'):  # check if child is a Tree
                """
                args is a Tree
                """
                if child.data == 'not':
                    return not self.visit(child.children[0])

                left = self.visit(child.children[0])
                right = self.visit(child.children[1])

                if child.data == 'and':
                    return left and right

                if child.data == 'or':
                    return left or right
            """
            args is a Token
            """
            if child.type == 'NAME':
                if child.value == 'true':
                    return True
                elif child.value == 'false':
                    return False
                else:
                    return self.vars[child.value]


class NoFlip(Transformer):
    """Remove flips from tree and replace them with a truth value.
       Used in branching for exact probability."""

    def __init__(self, var, val):
        self.val = val
        self.var = var
        self.found = False

    def flip(self, args):
        if args[0].value == self.var and not self.found:
            self.found = True
            return Tree('e', [Token('NAME', self.val)])
        else:
            return Tree('flip', args)


class NoDo(Transformer):
    """Remove do-operators from tree."""

    def __init__(self):
        pass

    def do(self, args):
        return lark.visitors.Discard()


class DoFlip(Transformer):
    """Intervene on a flip in a tree."""

    def __init__(self, old_tree, new_tree):
        self.old_f_token = old_tree.children[0].children[0]
        self.old_v_token = old_tree.children[0].children[1]
        self.new_tree = new_tree
        self.is_first = True

    def flip(self, args):
        args_match_old = args[0] == self.old_f_token and args[1] == self.old_v_token
        if args_match_old and self.is_first:
            self.is_first = False
            return self.new_tree.children[0]
        else:
            return Tree('flip', args)


class DoAssgn(Transformer):
    """Intervene on an assignment in a tree."""

    def __init__(self, old_tree, new_tree):
        self.old_f_token = old_tree.children[0].children[0]
        self.old_v_token = old_tree.children[0].children[1]
        self.new_tree = new_tree
        self.is_first = True

    def assgn(self, args):
        args_match_old = args[0] == self.old_f_token and args[1] == self.old_v_token
        if args_match_old and self.is_first:
            self.is_first = False
            return self.new_tree.children[0]
        else:
            return Tree('assgn', args)


def read(file_name):
    try:
        with open(file_name) as f:
            text = f.read()
            return text
    except(NameError, FileNotFoundError):
        print("Cannot open {}".format(file_name))
        return


def main():
    rifle_file = "rifleman.txt"
    read_file = read(rifle_file)
    file_tree = simppl_parser.parse(read_file)
    result = exact_prob(file_tree)
    print(result)


if len(sys.argv) > 1:
    method = sys.argv[1]
    file = sys.argv[2]
    text = read(file)
    parse_tree = simppl_parser.parse(text)
    if method == "enumerate":
        print(EnumerateSimPPL(parse_tree).enumerate())

    else:
        raise ValueError("Invalid inference type")

if __name__ == '__main__':
    main()
