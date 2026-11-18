-- Prove2me | solution 1 for TenChallenges.challenge_06
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-17T10:47:41.18314+00:00
-- url     : https://prove2.me/submissions/d361ab06-b74c-4e93-919f-768c61f2ba5b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_TenChallenges_Challenge_06
import Theorems.Thm_TenChallenges_challenge_06_all_graphs
import Theorems.Thm_TenChallenges_isAlphaWQO_of_reflecting_map

open TenChallenges in
theorem solution : ∀ r : Ordinal, TenChallenges.statement_06 r := by
  intro r
  unfold TenChallenges.statement_06
  split_ifs
  · exact isAlphaWQO_of_reflecting_map PlanarGraph.MinorLE FiniteGraph.MinorLE Subtype.val
      (fun _ _ h => h) (r / 2) (challenge_06_all_graphs (r / 2))
  · exact challenge_06_all_graphs (r / 2)
