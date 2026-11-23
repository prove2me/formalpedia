-- Prove2me | solution 1 for TenChallenges.challenge_06_all_graphs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-23T11:33:09.090397+00:00
-- url     : https://prove2.me/submissions/6938a6c1-4a8c-4710-937f-4eaa7e815ed4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_TenChallenges_AlphaWQO
import Theorems.Thm_TenChallenges_isAlphaWQO_of_omega_one
import Theorems.Thm_TenChallenges_challenge_06_all_graphs_omega_one

open TenChallenges in
theorem solution : ∀ α : Ordinal, IsAlphaWQO FiniteGraph.MinorLE α := fun α =>
  isAlphaWQO_of_omega_one FiniteGraph.MinorLE α challenge_06_all_graphs_omega_one
