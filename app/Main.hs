module Main (main) where

import Generator
import Data.Either (rights)
import Data.List (zip4)

-- extract :: [Either a b] -> [b]
-- extract (x:xs) =
--   case x of
--     Left _ -> extract xs
--     Right c -> c : extract xs

main :: IO ()
main = do
  let runs = map run examples
  let successes = rights runs
  let solved = map solve successes
  let comb = zip4 examples runs successes solved
  let comp = foldl (\acc (a, _, c, d) -> acc ++ [show a, show c, show d]) [] comb
  -- mapM_ print examples
  -- mapM_ print runs
  -- mapM_ print successes
  -- mapM_ print solved
  mapM_ putStrLn comp
