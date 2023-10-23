import Dpll
import Test.QuickCheck
import Data.List

type CNFFormula = [Clause]
type Clause = [Literal]


--dpll test

instance Arbitrary Proposition where
  arbitrary = elements $ map (Proposition . (: [])) ['p'..'u']

instance Arbitrary Literal where
  arbitrary = do
    p <- arbitrary
    elements [LProposition p, LNot p]

exhaustiveSolver :: CNFFormula -> Satisfiability
exhaustiveSolver [] = SAT
exhaustiveSolver cnf = if [] `elem` cnf
  then UNSAT
  else let 
    l = head . head $ cnf
    in case l of
      (LProposition p) -> mappend (exhaustiveSolver . deleteClause l . map (delete $ LNot p) $ cnf) (exhaustiveSolver . deleteClause (LNot p) . map (delete l) $ cnf)
      (LNot p) -> mappend (exhaustiveSolver . deleteClause l . map (delete $ LProposition p) $ cnf) (exhaustiveSolver . deleteClause (LProposition p) . map (delete l) $ cnf)

main :: IO ()
main = verboseCheck $ \cnf -> exhaustiveSolver cnf == dpll cnf --quickCheck $ \cnf -> exhaustiveSolver cnf == dpll cnf

{-

p = makeProposition "p"
q = makeProposition "q"
r = makeProposition "r"
s = makeProposition "s"
t = makeProposition "t"
u = makeProposition "u"

lp = makeLiteral p
lnp = makeNegateLiteral p
lq = makeLiteral q
lnq = makeNegateLiteral q
lr = makeLiteral r
lnr = makeNegateLiteral r
ls = makeLiteral s
lns = makeNegateLiteral s
lt = makeLiteral t
lnt = makeNegateLiteral t
lu = makeLiteral u
lnu = makeNegateLiteral u

testCNFFormula1 = [[lp], [lnp, lq], [lnp, lr]]
output1 = dpll testCNFFormula1

--[ [p], [Not p, q] , [Not p, r] ] -> [] SAT


testCNFFormula2 = [[lnp], [lp, lq], [lp, lr]]
output2 = dpll testCNFFormula2

--[ [Not p], [p, q] , [p, r] ] -> [] SAT

testCNFFormula3 = [[lp, lr], [lp, lq, lr], [lp, lnq]]
output3 = dpll testCNFFormula3

--[ [p, r], [p, q, r], [p, Not q]] -> [] SAT

testCNFFormula4 = [[lnp, lq], [lnp, lq, lr], [lp, lnr, lnq]]
output4 = dpll testCNFFormula4

--[ [Not p, q], [Not p, q, r], [p, Not r, Not q] ] -> [[Not p, q, r], [p, Not r, Not q]] -> [] SAT

testCNFFormula5 = [[lp, lnp]]
output5 = dpll testCNFFormula5

--[ [p, Not p] ] -> [] SAT

testCNFFormula6 = [[lp, lq], [lnp, lnq]]
output6 = dpll testCNFFormula6

-- [ [p, q], [Not p, Not q] ] -> [] SAT

testCNFFormula7 = [[lp, lq, lnr], [lp, lnq], [lnp], [lr, lq]]
output7 = dpll testCNFFormula7

-- [ [p, q, Not r], [p Not q], [Not p], [r q] ] -> [[]] UNSAT

testCNFFormula8 = [[ls, lt], [lns, lnt], [lp, lu], [lnp, lu]]
output8 = dpll testCNFFormula8

-- [ [s, t], [Not s, Not t], [p, u], [Not p, u] ] -> [] SAT

-}
