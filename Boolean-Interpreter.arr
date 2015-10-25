import s-exp as S
import lists as L
import sets as Se


###################################################
################### DATA TYPES ####################
###################################################
type Value = Boolean

## Interpretation Environment Binding (Eager)
data Binding:
  | bind(name :: String, val :: Value)
end

## List of Bindings is an Environment
type Environment = List<Binding>
mt-env = empty
xtnd-env = link


## Function Definition Core
data FunDefC:
  | fdC(name :: String, arg :: List<String>, body :: ExprC)
where:
  fdC("noArgs", [list: ],  xorC( trueC, falseC)) satisfies is-fdC
  fdC("oneArg", [list: "x"],  xorC( idC("x"), idC("x"))) satisfies is-fdC
  fdC("twoArgs", [list: "x", "y"],  xorC( idC("x"), idC("y"))) satisfies is-fdC
end



## Function Definition Ext
data FunDefExt:
  | fdExt(name :: String, args :: List<String>, body :: ExprExt)
where:
  fdExt("noArgs", [list: ],  andExt( [list: trueExt, falseExt])) satisfies is-fdExt
  fdExt("oneArg", [list: "x"],  andExt([list: idExt("x"), trueExt])) satisfies is-fdExt
  fdExt("twoArgs", [list: "x", "y"],  andExt([list: idExt("x"), idExt("y")])) satisfies is-fdExt
end


## Extended Language Expressions
data ExprExt:
  | trueExt
  | falseExt
  | notExt(e :: ExprExt)
  | orExt(rands :: List<ExprExt>)
  | xorExt(rands :: List<ExprExt>)
  | andExt(rands :: List<ExprExt>)
  | norExt(rands :: List<ExprExt>)
  | nandExt(rands :: List<ExprExt>)
  | xnorExt(rands :: List<ExprExt>)
  | ifExt(c :: ExprExt, t :: ExprExt, e :: ExprExt)
  | idExt(s :: String)
  | appExt(name :: String, arg :: List<ExprExt>)
  | condExt(rands :: List<ExprPair>)
where:
  trueExt satisfies is-trueExt
  falseExt satisfies is-falseExt
  notExt(trueExt) satisfies is-notExt
  orExt([list: orExt([list: trueExt, trueExt]), trueExt]) satisfies is-orExt
  xorExt([list: orExt([list: trueExt, trueExt]), trueExt]) satisfies is-xorExt
  andExt([list: xorExt([list: trueExt, trueExt]), trueExt]) satisfies is-andExt
  norExt([list: nandExt([list: trueExt, trueExt]), trueExt]) satisfies is-norExt
  nandExt([list: andExt([list: trueExt, trueExt]), trueExt]) satisfies is-nandExt
  xnorExt([list: orExt([list: trueExt, trueExt]), trueExt]) satisfies is-xnorExt
  ifExt(trueExt, falseExt, trueExt) satisfies is-ifExt
  idExt("a") satisfies is-idExt
  condExt([list: pairExt(trueExt, falseExt)]) satisfies is-condExt
  appExt("f", [list: trueExt, falseExt]) satisfies is-appExt
end

## Core Language Expressions
data ExprC:
  | trueC
  | falseC
  | xorC(l :: ExprC, r :: ExprC)
  | ifC(c :: ExprC, t :: ExprC, e :: ExprC)
  | idC(s :: String)
  | appC(name :: String, args :: List<ExprC>)
where:
  trueC satisfies is-trueC
  falseC satisfies is-falseC
  xorC(trueC, falseC) satisfies is-xorC
  ifC(trueC, falseC, trueC) satisfies is-ifC
  idC("a") satisfies is-idC
  appC("f", [list: trueC ]) satisfies is-appC
end


## Expression Pair (Used in conditionals)
data ExprPair:
  | pairExt(l :: ExprExt, r :: ExprExt)
where:
  pairExt(trueExt, falseExt) satisfies is-pairExt
  pairExt(orExt([list: trueExt, trueExt]), xorExt([list: trueExt, trueExt])) satisfies is-pairExt
end

###################################################
################### HELPERS #######################
###################################################

## Function: get-fundef
## Input: String, List<FunDefC>
## Output: FunDefC
## Description: If function name exists, return function, otherwise
## return error
fun get-fundef(name :: String, fds :: List<FunDefC>)
  -> FunDefC:
  cases (List<FunDefC>) fds:
    | empty => raise("couldn't find function")
    | link(f, r) =>
      if f.name == name:
        f
      else:
        get-fundef(name, r)
      end
  end
where:
  f1 = fdC("a",  [list: "x"], xorC(idC("x"), idC("x")))
  get-fundef("a", [list: f1]) is f1
  get-fundef("b", [list: ]) raises("couldn't find function")
end


## Function: subst
## Input: Value, String, ExprC
## Output: ExprC
## Description:
fun subst(w :: Value, at :: String, in :: ExprC) -> ExprC:
  cases (ExprC) in:
    | trueC => trueC
    | falseC => falseC
    | ifC(cnd, thn, els) =>
      ifC(subst(w, at, cnd), subst(w, at, thn), subst(w, at, els))
    | appC(f, a) => appC(f, subst(w, at, a))
    | idC(s) =>
      if s == at:
        w
      else:
        in
      end
  end
end

## Function: lookup
## Input: String, Enviroment
## Output: Value
## Description: Lookup identifier to see if it exists in
## current enviroment, otherwise it is an unbound identifier
fun lookup(s :: String, nv :: Environment) -> Value:
  cases (List) nv:
    | empty => raise("unbound identifier: " + s )
    | link(f, r) =>
      if s == f.name:
        f.val
      else:
        lookup(s, r)
      end
  end
where:
  lookup("x", empty) raises("unbound")
  lookup("x", [list: bind("x", true)]) is true
end


###################################################
################### PARSERS #######################
###################################################



## Function: parse-expr
## Input: S.S-Exp
## Output: ExprExt
## Description: Parse s-exp into base case or hand off to parse helper function
fun parse-expr(s :: S.S-Exp) -> ExprExt:
  cases (S.S-Exp) s:
    | s-sym(e) =>
      if e == "true":
        trueExt
      else if e == "false":
        falseExt
      else:
        idExt(e)
      end
    | s-str(e) =>
      raise("error")
    | s-list(shadow s) => parse-list(s)
    | else => raise("parse: not bool or expression " + s)
  end
where:
  fun p(s): parse-expr(S.read-s-exp(s)) end
  p("true") is trueExt
  p("false") is falseExt
  p("x") is idExt("x")
end

## Function: parse-list
## Input: List<S.S-Exp>
## Output: ExprExt
## Description: Parse a list of s-exp into boolean operation of hand off to parse helper
fun parse-list(l :: List<S.S-Exp>) -> ExprExt:
  cases (List<S.S-Exp>) l:
    | empty => raise("Unexpected empty list")
    | link(fst,rst) =>
      if (fst == S.s-sym("not")) and (rst.length() == 1):
        notExt(parse-expr(L.index(rst,0)))
      else if (fst == S.s-sym("if")) and (rst.length() == 3):
        parse-if(rst)
      else if (fst == S.s-sym("if")) and (rst.length() > 3):
        listOfPairs = [list: pairExt(parse-expr(L.index(rst, 0)), parse-expr(L.index(rst, 1)))]
        body = rst.take(rst.length() - 1).drop(2)

        if (L.all(lam(n): (S.is-s-list(n)) and
              (n.exps.length() == 3) and
              (L.index(n.exps,0) == S.s-sym("elif")) end, body)) and
          (S.is-s-list(rst.last())) and
          (rst.last().exps.length() == 2) and
          (L.index(rst.last().exps, 0) == S.s-sym("else")):

          listOfPairs.append(L.fold(lam(acc, curr):
              link(pairExt(parse-expr(L.index(curr.exps, 1)), parse-expr(L.index(curr.exps,2))), acc) end, [list: pairExt(trueExt, parse-expr(L.index(rst.last().exps, 1)))], body))

          condExt(listOfPairs)
        else:
          raise("error")
        end
      else if fst == S.s-sym("and"):
        andExt(L.map(parse-expr, rst))
      else if fst == S.s-sym("or"):
        orExt(L.map(parse-expr, rst))
      else if fst == S.s-sym("xor"):
        xorExt(L.map(parse-expr, rst))
      else if fst == S.s-sym("nor"):
        norExt(L.map(parse-expr, rst))
      else if fst == S.s-sym("nand"):
        nandExt(L.map(parse-expr, rst))
      else if fst == S.s-sym("xnor"):
        xnorExt(L.map(parse-expr, rst))
      else:
        raise("invalid operator " + fst.s)
      end
  end
where:
  fun p(s): parse-expr(S.read-s-exp(s)) end
  p("true") is trueExt
  p("(not true)") is notExt( trueExt)
  p("(or true false)") is orExt([list: trueExt, falseExt])
  p("(and true false)") is andExt([list: trueExt, falseExt])
  p("(xor true false)") is xorExt([list: trueExt, falseExt])
  p("(nor true false)") is norExt([list: trueExt, falseExt])
  p("(nand true false)") is nandExt([list: trueExt, falseExt])
  p("(xnor true false)") is xnorExt([list: trueExt, falseExt])

  parse-list([list: S.s-sym("nor"),
      S.s-list([list: S.s-sym("or"), S.s-sym("true"), S.s-sym("false")]), S.s-sym("true")])
    is norExt([list: orExt([list: trueExt, falseExt]), trueExt])
  p("(if true false (elif true false) (else true))")
  p("(hello true false)") raises("invalid")
end

## Function: parse-if
## Input: List<S.S-Exp>
## Output: ExprExt
## Description: Parse a list of s-exp into the body of an if-statement
fun parse-if(args :: List<S.S-Exp>) -> ExprExt:
  cases (List<S.S-Exp>) args:
    | empty => raise("Unexpected empty list")
    | else =>
      c = parse-expr(L.index(args,0))
      t = parse-expr(L.index(args,1))
      e = parse-expr(L.index(args,2))
      ifExt(c,t,e)
  end
end

## Function: parse-def
## Input: List<S.S-Exp>
## Output: FunDefExt
## Description: Parse a single function definition (as an s-expression)
fun parse-def(adef :: S.S-Exp) -> FunDefExt:
  cases (S.S-Exp) adef:
    | s-list(shadow adef) =>
      cases (List) adef:
        | empty => raise("function def w/o arguments")
        | link(op, args) =>
          if (op == S.s-sym("fun")) and (args.length() == 2):
            def = L.index(args, 0).exps
            body = L.index(args,1)
            name = L.index(def,0).s
            listOfArgs = L.map(lam(x): x.s end, def.drop(1))
            if Se.list-to-list-set(listOfArgs).size() == listOfArgs.length():
              fdExt(name, listOfArgs, parse-expr(body))
            else:
              raise("duplicate variable names")
            end
          else:
            raise("invalid op or length")
          end
      end
  end
where:
  fun p(s): parse-def(S.read-s-exp(s)) end
  p("(fun (main x y z) (xor  x y z))") is fdExt("main",[list: "x", "y", "z"], xorExt([list: idExt("x"), idExt("y"), idExt("z")]))

  ## TODO
  #p("(fun (true x y z) (xor  x y z))") raises("error, keyword cannot be used as function name")
end

###################################################
################### DESUGARERS ####################
###################################################

## Function: desugar-expr
## Input: ExprExt
## Output: ExprC
## Description: Desugar extended language to appropriate core language
fun desugar-expr(expr :: ExprExt) -> ExprC:
  cases (ExprExt) expr:
    | trueExt => trueC
    | falseExt => falseC
    | idExt(l) => idC(l)
    | ifExt(c, t, e) => ifC(desugar-expr(c), desugar-expr(t), desugar-expr(e))
    | xorExt(l) => L.fold(lam(acc, curr): xorC(desugar-expr(curr), acc) end, falseC, l)
    | xnorExt(l) => desugar-expr(notExt(xorExt(l)))
    | andExt(l) => L.fold(lam(acc, curr): ifC(desugar-expr(curr),acc, falseC) end, trueC, l)
    | nandExt(l) => L.fold(lam(acc, curr): ifC(ifC(desugar-expr(curr),acc, falseC), falseC, trueC) end, trueC, l)
    | orExt(l) => L.fold(lam(acc, curr): ifC(desugar-expr(curr), trueC, acc) end, falseC, l)
    | norExt(l) => L.fold(lam(acc, curr): ifC(ifC(desugar-expr(curr), trueC, acc), falseC, trueC) end, falseC, l)
    | notExt(l) => ifC(desugar-expr(l), falseC, trueC)
    | fdExt(n, args, b) => fdC(n, args, desugar-expr(b))
    | condExt(l) =>
      fstToLast = L.index(l,l.length() - 2)
      last = L.index(l,l.length() - 1)
      a = desugar-expr(fstToLast.l)
      b = desugar-expr(fstToLast.r)
      c = desugar-expr(last.r)
      L.fold(lam(acc, curr): ifC(desugar-expr(curr.l), desugar-expr(curr.r), acc) end, ifC(a,b,c), l.take(l.length() - 2))
  end
where:
  fun p(s): desugar-expr(s) end
  ## ifExt
  p(ifExt(trueExt, falseExt, trueExt)) is ifC(trueC, falseC, trueC)
  ## xorExt
  p(xorExt([list: falseExt, trueExt])) is xorC(trueC, xorC(falseC, falseC))
  ## xnorExt returning wrong value
  p(xnorExt([list: falseExt, falseExt])) is ifC(xorC(falseC,xorC(falseC,falseC)),falseC,trueC)
  ## andExt
  p(andExt([list: falseExt, trueExt])) is ifC(trueC, ifC(falseC, trueC, falseC), falseC)
  ## nandExt
  p(nandExt([list: falseExt, falseExt])) is ifC(ifC(falseC, ifC(ifC(falseC, trueC, falseC), falseC, trueC), falseC), falseC, trueC)
  ## orExt
  p(orExt([list: falseExt, falseExt])) is ifC(falseC, trueC, ifC(falseC, trueC, falseC))
  ## norExt
  p(norExt([list: falseExt, trueExt])) is ifC(ifC(trueC, trueC, ifC(ifC(falseC, trueC, falseC), falseC, trueC)), falseC,trueC)
  ## notExt
  p(notExt(trueExt)) is ifC(trueC, falseC, trueC)
  ## condExt
  p(condExt([list: pairExt(falseExt, falseExt), pairExt(trueExt, falseExt)])) is ifC(falseC,falseC,falseC)
end



## Function: desugar-def
## Input: FunDefExt
## Output: FunDefC
## Description: Desugar a single function definition to a core function definition
fun desugar-def(def :: FunDefExt) -> FunDefC:
  cases (FunDefExt) def:
    | fdExt(n, a, b) =>
      fdC(n, a, desugar-expr(b))
  end
where:
  fun p(s): desugar-def(s) end
  p(fdExt("noArg", [list: ], xorExt([list: trueExt, trueExt]))) is fdC("noArg",[list: ], xorC(trueC, xorC(trueC,falseC)))

  p(fdExt("myFun", [list: "x"], xorExt([list: idExt("x"), trueExt]))) is fdC("myFun",[list: "x"], xorC(trueC, xorC(idC("x"),falseC)))
end


###################################################
################### INTERPRETERS ##################
###################################################



## Function: interp-expr
## Input: ExprC, Enviroment, List<FunDefC>
## Output: Value
## Description: Interprets an entire expression into a single value (true/false)
fun interp-expr(e :: ExprC, nv :: Environment, fds :: List<FunDefC>) -> Value:
  cases (ExprC) e:
    | trueC => true
    | falseC => false
    | ifC(c, thn, els) =>
      ic = interp-expr(c, nv, fds)
      if ic:
        interp-expr(thn, nv, fds)
      else:
        interp-expr(els, nv, fds)
      end
    | idC(s) => lookup(s, nv)
    | appC(f, a) =>
      fd = get-fundef(f, fds)
      interp-arg = lam(arg): interp-expr(arg, nv, fds) end

      arg-vals = map(interp-arg, a)
      arg-list-folder = lam(acc,nm,v): xtnd-env(bind(nm,v),acc) end
      if Se.list-to-list-set(fd.arg).size() == fd.arg.length():
        new-env = fold2(arg-list-folder, mt-env, fd.arg, arg-vals)
        interp-expr(fd.body, new-env, fds)
      else:
        raise("duplicate variable names in function declaration")
      end
    | xorC(l,r) =>
      p = interp-expr(l, nv, fds)
      q = interp-expr(r, nv, fds)
      (p or q) and not(p and q)
  end
where:
  interp-expr(ifC(trueC, trueC, falseC), mt-env, empty) is true
  f1 = fdC("a",  [list: "x"], xorC(idC("x"), idC("x")))
  f2 = fdC("b", [list: "x","y","z"], ifC(idC("x"), idC("y"), idC("z")))
  f3 = fdC("c", [list: "x", "y"], ifC(xorC(idC("x"), falseC), idC("y"), falseC))
  f4 = fdC("d", [list: "x", "x"], ifC(xorC(idC("x"), falseC), idC("x"), falseC))

  funs = [list: f1, f2, f3, f4]
  fun i(e): interp-expr(e, mt-env, funs) end

  i(appC("a",  [list: trueC])) is false
  i(appC("b",[list: trueC, falseC, trueC])) is false
  i(appC("c", [list: xorC(trueC, falseC), trueC])) is true
  i(appC("d", [list: xorC(trueC, falseC), trueC])) raises("dup")
end








### ****************** ALL-IN-ONE Functions ***********************

## Allows "main function" style programming. Programs are expected to be
## a list of definitions one of which is  a function named "main".
## main may take any number of arguments. run-main
## accepts main's arguments "at the CLI" and runs main
## with those arguments
fun run-main(prog :: String, args :: List<S.S-Exp>) -> Value:
  ## parse the "list of definitions"
  func = S.read-s-exp(prog)
  funs = func.exps
  cases (List<S.S-Exp>) funs:
    | empty => raise("unexpected empty list")
    | else =>
      ## parse each def
      defs = map(lam(d): desugar-def(parse-def(d)) end, funs)
      arg = map(lam(d): desugar-expr(parse-expr(d)) end, args)

      ## run main with the given arguments
      interp-expr(appC("main", arg), mt-env, defs)
  end
where:
  ## main is really just an echo or identity function
  # fdC(name :: String, arg :: List<String>, body :: ExprC)

  run-main("((fun (main x y z) (xor  x y z)))",[list: S.s-sym("true"), S.s-sym("false"), S.s-sym("true")]) is false
  run-main("((fun (main x y z) (xor x y z)))",[list:  S.s-sym("true"), S.s-sym("true"), S.s-sym("true")]) is true
  run-main("((fun (main x y z) (xor x y z)))",[list:  S.s-sym("true"), S.s-sym("false"), S.s-sym("false")]) is true
end
