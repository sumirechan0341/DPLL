-- DPLL Algorithm

--BNF of the Formula

--Prop := Prop String
--Formula := Prop | AND Formula Formula | OR Formula Formula | Not Formula | Cond Formula Formula |　BiCond Formula Formula | TRUE | FALSE
--Clause := Prop | OR Clause Clause
--CNF_Formula := Prop | AND Clause Clause

module Dpll(
    dpll,
    makeLiteral,
    makeNegateLiteral,
    makeProposition,
    printCNFFormula,
    modelGenerator,
    printModel,
    dpllS,
    deleteClause,
    Proposition(..),
    Literal(..),
    Satisfiability(..)
) where


import Data.List
import Control.Monad.State
import Data.Ord

newtype Proposition = Proposition String deriving(Eq, Ord)
data Satisfiability = SAT | UNSAT deriving (Show, Eq)
data AnalysisState = STrue | SFalse deriving (Show, Eq)
data Literal = LProposition Proposition | LNot Proposition deriving(Eq, Ord)

instance Show Proposition where
  show (Proposition name) = name

instance Show Literal where
  show (LProposition p) = show p
  show (LNot p) = show "!" ++ show p


type CNFFormula = [Clause]
type Clause = [Literal]
type LiteralAssignment = (Literal, Int)
type Strategy = CNFFormula -> CNFFormula

instance Monoid Satisfiability where
    mempty = UNSAT
    mappend SAT _ = SAT
    mappend _ SAT = SAT
    mappend UNSAT UNSAT = UNSAT


--dpll

dpll :: CNFFormula -> Satisfiability
dpll cnf
    | null cnf' = SAT -- Not exist any clauses
    | [] `elem` cnf' = SAT -- exist some empty clauses
    | positiveRoot == SAT = SAT -- exist satisfiabile assignment in positiveRoot
    | otherwise = negativeRoot -- Not exist satisfiabile assignment in positiveRoot and then, search in negativRoot
    where positiveRoot = caseAnalysis cnf' l STrue
          negativeRoot = caseAnalysis cnf' l SFalse
          l = head $ head cnf'
          cnf' = simplify cnf

-- analysis function

caseAnalysis :: CNFFormula -> Literal -> AnalysisState -> Satisfiability
caseAnalysis cnf l STrue = dpll $ unitCutL cnf l -- assign true to l
caseAnalysis cnf l SFalse = dpll . unitCutL cnf $ literalNagation l  -- assign false to l

--rules of cut

simplify :: CNFFormula -> CNFFormula
simplify = cleanUp . subsumptionCut . pureCut . unitCut

cleanUp :: CNFFormula -> CNFFormula
cleanUp = filter (not . isTautology)

subsumptionCut :: CNFFormula -> CNFFormula
subsumptionCut [] = []
subsumptionCut cnf =
    let containList = [[x, y]|x <- cnf, y <- cnf, null (x \\ y), x /= y]
    in cnf \\ [y | [_ ,y] <- containList]

pureCut :: CNFFormula -> CNFFormula
pureCut cnf = foldl (flip deleteClause) cnf (searchPureLiteral . nub . concat $ cnf)

unitCut :: CNFFormula -> CNFFormula
unitCut cnf = foldl unitCutL cnf $ searchUnitLiteral cnf


-- assistant functions of cutting

unitCutL :: CNFFormula -> Literal -> CNFFormula
unitCutL cnf (LProposition p) = map (delete $ LNot p) $ deleteClause (LProposition p) cnf
unitCutL cnf (LNot p) = map (delete $ LProposition p) $ deleteClause (LNot p) cnf

deleteClause :: Literal -> CNFFormula -> CNFFormula
deleteClause l = filter (\c -> l `notElem` c)

isTautology :: Clause -> Bool
isTautology [] = False
isTautology (l:clause) = case l of
    (LProposition p) -> LNot p `elem` clause || isTautology clause
    (LNot p) -> LProposition p `elem` clause || isTautology clause


--make new state function

makePositiveLiterals :: [Literal] -> [Literal]
makePositiveLiterals ls = nub $ map literal2PosLiteral ls

literalNagation :: Literal -> Literal
literalNagation (LProposition p) = LNot p
literalNagation (LNot p) = LProposition p

literal2PosLiteral :: Literal -> Literal
literal2PosLiteral (LNot p) = LProposition p
literal2PosLiteral l = l

--search function

searchPureLiteral :: [Literal] -> [Literal]
searchPureLiteral [] = []
searchPureLiteral (l : literalList) =
  let
    searchNextLiteral = searchPureLiteral $ tail literalList
    in case l of
        LProposition p -> if LNot p  `notElem` literalList then l : searchNextLiteral else searchPureLiteral $ delete (LNot p) (tail literalList)
        LNot p -> if LProposition p `notElem` literalList then l : searchNextLiteral else searchPureLiteral $ delete (LProposition p) (tail literalList)

searchUnitLiteral :: CNFFormula -> [Literal]
searchUnitLiteral [] = []
searchUnitLiteral cnf =  let
    c = head cnf
    searchNextLiteral = searchUnitLiteral $ tail cnf
    in case length c of
        1 -> c ++ searchNextLiteral
        _ -> searchNextLiteral

nubL :: [Literal] -> [Literal]
nubL [] = []
nubL (LProposition l : ls) = LProposition l : nubL ls
nubL (LNot l : ls) = nubL ls

--make function

makeProposition :: String -> Proposition
makeProposition = Proposition

makeLiteral :: Proposition -> Literal
makeLiteral = LProposition

makeNegateLiteral :: Proposition -> Literal
makeNegateLiteral = LNot


-- print function

printCNFFormula :: CNFFormula -> IO ()
printCNFFormula = mapM_ (print . clause2String)

printModel :: Maybe [LiteralAssignment] -> String
printModel Nothing = "UNSAT"
printModel (Just las) = unwords $ map assignment2String las

clause2String :: Clause -> [String]
clause2String = map literal2String

literal2String :: Literal -> String
literal2String (LProposition (Proposition name)) = name
literal2String (LNot (Proposition name)) = "Not " ++ name

assignment2String :: LiteralAssignment -> String
assignment2String (LProposition (Proposition name), 1) = "{" ++ name ++ " : " ++ "1" ++ "}"
assignment2String (LProposition (Proposition name), 0) = "{" ++ name ++ " : " ++ "0" ++ "}"


--function for State Monad

pruningS :: Strategy -> (CNFFormula -> CNFFormula -> [LiteralAssignment]) -> CNFFormula -> State [LiteralAssignment] CNFFormula
pruningS strategy solveAssignment cnf = do
  let cnf' = strategy cnf
  if cnf' /= cnf
    then do
      literalEnv <- get
      put $ literalEnv ++ solveAssignment cnf cnf'
      return cnf'
    else return cnf'

unitCutS :: CNFFormula -> State [LiteralAssignment] CNFFormula
unitCutS cnf = pruningS unitCut $
  \cnf cnf' ->
    let
      cnf'' = cnf \\ cnf'
      unitLiterals = searchUnitLiteral cnf''
      u_literalAssignment = map assignment1 unitLiterals
    in
      u_literalAssignment ++ map assignment1 $ nub . makePositiveLiterals $ (nub . makePositiveLiterals $ ((nub . concat $ cnf) \\ unitLiterals)) \\ (nub . makePositiveLiterals $ (nub . concat $ cnf'))


pureCutS :: CNFFormula -> State [LiteralAssignment] CNFFormula
pureCutS cnf = pruningS pureCut $
  \cnf cnf' ->
    let
      pureLiterals = searchPureLiteral . nub . concat $ cnf
      p_literalAssignment = map assignment1 pureLiterals
    in
      p_literalAssignment ++ map assignment1 $ nub . makePositiveLiterals $ (nub . makePositiveLiterals $ ((nub . concat $ cnf) \\ pureLiterals )) \\ (nub . makePositiveLiterals $ (nub . concat $ cnf'))

subsumptionCutS :: CNFFormula -> State [LiteralAssignment] CNFFormula
subsumptionCutS cnf = pruningS subsumptionCut $
  \cnf cnf' ->
    map assignment1 $ (nub . makePositiveLiterals . concat $ cnf) \\ (nub . makePositiveLiterals . concat $ cnf')

cleanUpS :: CNFFormula -> State [LiteralAssignment] CNFFormula
cleanUpS cnf = pruningS cleanUp $
  \cnf cnf' ->
    map assignment1 . makePositiveLiterals $ (nub . makePositiveLiterals . concat $ cnf) \\ (nub . makePositiveLiterals . concat $ cnf')

simplifyS :: CNFFormula -> State [LiteralAssignment] CNFFormula
simplifyS cnf = pureCutS cnf >>= unitCutS >>= cleanUpS >>= subsumptionCutS

dpllS :: CNFFormula -> State [LiteralAssignment] Satisfiability
dpllS cnf = do
    las <- get
    let
        cnf' = evalState (simplifyS cnf) las
        l = head $ head cnf'
        positiveRoot = caseAnalysis cnf' l STrue
        negativeRoot = caseAnalysis cnf' l SFalse
    if null cnf'
        then do
            put $ execState (simplifyS cnf) las
            return SAT
        else if [] `elem` cnf'
            then do
                --put $ execState (simplifyS cnf) las
                put []
                return UNSAT
            else if positiveRoot == SAT
                then do
                    put $ execState (simplifyS cnf) las ++ [assignment1 l]
                    dpllS $ unitCutL cnf' l
                else do
                    put $ execState (simplifyS cnf) las ++ [assignment0 l]
                    dpllS . unitCutL cnf' $ literalNagation l

-- modelGenerator

modelGenerator :: CNFFormula -> Maybe [LiteralAssignment]
modelGenerator cnf = case evalState (dpllS cnf) [] of
    UNSAT -> Nothing
    SAT -> Just . sortBy (comparing fst) $ execState (dpllS cnf) []
    -- sortBy (comparing fst) <==> Data.List.sortOn fst (from ghc7.10.1)


-- literal assignment

assignment1 :: Literal -> LiteralAssignment
assignment1 l@(LProposition p) = (l, 1)
assignment1 (LNot p) = (makeLiteral p, 0)

assignment0 :: Literal -> LiteralAssignment
assignment0 l@(LProposition p) = (l, 0)
assignment0 (LNot p) = (makeLiteral p, 1)
