--
-- Maxim Puchkov
-- 301314335
-- CMPT 384 Assignment 2
--
-- Parsing, unparsing, deriving, simplifying
-- mathematical expressions
--

import System.Environment
import System.IO (stdout,stderr,hPutStr,hPutStrLn)
import Data.Char
import Data.List





-- Data type for mathematical expressions

data ME = Num Int
          | Var Char
          | Group ME
          | Sum [ME]
          | Product [ME]
          | Power ME Int
          | Neg ME
          deriving (Show, Ord, Eq)






-- Derivation

deriv :: ME -> Char -> ME
deriv (Num me) c = Num 0
deriv (Var me) c
  | me == c    = Num 1
  | otherwise  = Num 0
deriv (Group me) c = Group (deriv me c)
deriv (Sum me) c = Sum ([deriv el c | el <- me])
deriv (Product me) c = Sum ([Product [deriv el c, Group (Product (delete el me))] | el <- me])
deriv (Power me n) c = Product [(Product [Num n, Power me (n-1)]), deriv me c]
deriv (Neg me) c = Neg (deriv me c)


--deriv (Power me n) c = deriv (Product [me | i <- [0..n-1]]) c
--deriv (Product (i:n:[])) c = Sum [Product [n, deriv i c], Product [i, deriv n c]]
--deriv (Product (i:me)) c = Sum [Product (me ++ [deriv i c]), Product [i, deriv (Product me) c]]





-- Simplification

simplifyME :: ME -> ME
add :: ME -> ME -> ME
mul :: ME -> ME -> ME


simplifyME (Num me)
  | me < 0    = Neg (Num (-me))
  | otherwise = Num me
simplifyME (Var me) = Var me
simplifyME (Group me) = Group (simplifyME me)
simplifyME (Power me n) = Power (simplifyME me) n
simplifyME (Sum (i:n:[])) = add (simplifyME i) (simplifyME n)
simplifyME (Sum (i:me)) = add (simplifyME i) (simplifyME (Sum me))
simplifyME (Product (i:n:[])) = mul (simplifyME i) (simplifyME n)
simplifyME (Product (i:me)) = mul (simplifyME i) (simplifyME (Product me))
simplifyME (Neg me) = Neg (simplifyME me)
simplifyME me = me


add me (Num 0) = me
add me (Neg (Num 0)) = me
add (Num 0) (Neg (me)) = Neg (me)
add (Group me1) me2 = add me1 me2
add me1 (Group me2) = add me1 me2
add (Num m) (Num n) = simplifyME (Num (m+n))
add (Num m) (Neg (Num n)) = add (Num m) (Num (-n))
add (Neg (Num m)) (Num n) = add (Num (-m)) (Num n)
add (Neg (Num m)) (Neg (Num n)) = add (Num (-m)) (Num (-n))
add (Neg (Num n)) me = add me (Neg (Num n))
add (Num n) me = add me (Num n)
add (Sum me1) (Sum me2) = simplifyME (Sum (me1 ++ me2))
add (Sum me) (Num n) = simplifyME (Sum (me ++ [Num n]))
add (Sum me) (Neg (Num n)) = simplifyME (Sum (me ++ [Neg (Num n)]))
add (Sum me1) me2 = (Sum ([me2] ++ me1))
add me1 (Sum me2) = (Sum ([me1] ++ me2))
add me1 me2 = Sum [me1, me2]


mul (Num 0) me = Num 0
mul (Num 1) me = me
mul me1 (Group (Product me2)) =
  Product [Group (simplifyME (Product ([me1] ++ (init me2)))),head (reverse me2)]
mul (Group me1) me2 = mul me1 me2
mul me1 (Group me2) = mul me1 me2
mul (Num m) (Num n) = Num(m*n)
mul (Neg (Num m)) (Num n) = Neg (Num(m*n))
mul (Num m) (Neg (Num n)) = Neg (Num(m*n))
mul (Neg (Num m)) (Neg (Num n)) = Num(m*n)
mul me (Num n) = mul (Num n) me
mul me (Neg (Num n)) = mul (Neg (Num n)) me
mul (Num n) (Product ((Num m):me)) =
  simplifyME (Product ([mul (Num n) (Num m)] ++ me))


--mul (Product me1) (Sum me2) = simplifyME (Sum [mul e1 e2 | e1 <- me1, e2 <- me2])

mul me1 (Product me2) = Product ([me1] ++ me2)
mul (Product me1) me2 = Product ([me2] ++ me1)
mul (Power me1 n) me2
  | me1 == me2 = Power me1 (n+1)
  | otherwise = Product [me1, me2]
mul me1 me2
  | me1 == me2 = Power me1 2
  | otherwise  = Product [me1, me2]





-- Parser

stoi :: [Char] -> Int
digits :: [Char] -> [Char]
parseNumeral :: [Char] -> Maybe (ME, [Char])
parseVariable :: [Char] -> Maybe (ME, [Char])
parseElement :: [Char] -> Maybe (ME, [Char])
parseFactor :: [Char] -> Maybe (ME, [Char])
parseTerm :: [Char] -> Maybe (ME, [Char])
extendTerm :: (ME, [Char]) -> Maybe (ME, [Char])
parseExpression :: [Char] -> Maybe (ME, [Char])
extendExpression :: (ME, [Char]) -> Maybe (ME, [Char])
parseME :: [Char] -> Maybe ME


stoi str = read str :: Int


digits [] = []
digits (s:more)
  | isDigit s = [s] ++ digits more
  | otherwise = []


parseNumeral [] = Nothing
parseNumeral s =
  let d = digits s
      l = length d
      more = drop l s in
  case l of
    0 -> Nothing
    _ -> Just (Num (stoi d), more)


parseVariable [] = Nothing
parseVariable (s:more)
  | isLetter s  = Just (Var s, more)
  | otherwise   = Nothing


parseElement [] = Nothing
parseElement ('(':more) =
  case parseExpression(more) of
    Just (me, ')':m) -> Just (Group me, m)
    _ -> Nothing
parseElement ('-':'(':more) =
  case parseExpression(more) of
    Just (me, ')':m) -> Just (Neg (Group me), m)
    _ -> Nothing
parseElement ('-':c:s)
  | isDigit c = case parseNumeral(c:s) of
    Just (n, m) -> Just (Neg n, m)
    _ -> Nothing
  | isLetter c = case parseVariable(c:s) of
    Just (v, m) -> Just (Neg v, m)
    _ -> Nothing
  | otherwise = Nothing
parseElement (c:s)
  | isDigit c   = parseNumeral(c:s)
  | isLetter c  = parseVariable(c:s)
  | otherwise   = Nothing


parseFactor [] = Nothing
parseFactor s =
  case parseElement(s) of
    Just (e, '*':'*':more) -> case parseElement(more) of
      Just (Neg (Num n), m) -> Just (Power e (-n), m)
      Just (Num n, m) -> Just (Power e n, m)
      _ -> Nothing
    Just (e, more) -> Just (e, more)
    _ -> Nothing


parseTerm [] = Nothing
parseTerm s =
  case parseFactor(s) of
    Just (me, more) -> extendTerm(me, more)
    _ -> Nothing


extendTerm(me, []) = Just (me, [])
extendTerm(Product me, '*':more) =
  case parseFactor(more) of
    Just (e, m) -> extendTerm(Product (me ++ [e]), m)
    _ -> Nothing
extendTerm(me, '*':more) =
  case parseFactor(more) of
    Just (e, m) -> extendTerm(Product [me, e], m)
    _ -> Nothing
extendTerm(me, more) = Just (me, more)


parseExpression s =
  case parseTerm(s) of
    Just (me, more) -> extendExpression(me, more)
    _ -> Nothing


extendExpression(me, []) = Just (me, [])
extendExpression(Sum me, '+':more) =
  case parseTerm(more) of
    Just (e, m) -> extendExpression(Sum (me ++ [e]), m)
    _ -> Nothing
extendExpression(Sum me, '-':more) =
  case parseTerm(more) of
    Just (e, m) -> extendExpression(Sum (me ++ [Neg e]), m)
    _ -> Nothing
extendExpression(me, '+':more) =
  case parseTerm(more) of
    Just (e, m) -> extendExpression(Sum [me, e], m)
    _ -> Nothing
extendExpression(me, '-':more) =
  case parseTerm(more) of
    Just (e, m) -> extendExpression(Sum [me, (Neg e)], m)
    _ -> Nothing
extendExpression(me, more) = Just (me, more)


parseME s =
  case parseExpression(s) of
    Just(me, []) -> Just me
    _ -> Nothing





-- Unparser


isNeg :: ME -> Bool
isNeg (Neg me) = True
isNeg (me) = False


unparseME :: ME -> [Char]
unparseME (Num me) = show me
unparseME (Var me) = [me]
unparseME (Group me) = "(" ++ unparseME me ++ ")"
unparseME (Sum []) = []
unparseME (Sum (i:[])) = unparseME i
unparseME (Sum (i:n:me)) = unparseME i ++ sign ++ unparseME(Sum ([n] ++ me))
  where sign = if (not (isNeg n)) then "+" else ""
unparseME (Product []) = []
unparseME (Product (i:me))
  | me /= []  = unparseME i ++ "*" ++ unparseME(Product me)
  | otherwise = unparseME i
unparseME (Power me n) = unparseME me ++ "**" ++ show n
unparseME (Neg me) = "-" ++ unparseME me





-- Main Program

parse_deriv_simp_unparse v s =
  case parseME s of
    Just e -> Just (unparseME (simplifyME (deriv e v)))
    _ -> Nothing

main = do
  [[v], expr] <- getArgs
  case parse_deriv_simp_unparse v expr of
    Just s -> hPutStrLn stdout s
    _ -> hPutStrLn stdout "Parse failure"
