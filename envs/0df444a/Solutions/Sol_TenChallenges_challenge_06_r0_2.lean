-- Prove2me | solution 2 for TenChallenges.challenge_06_r0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-17T15:27:12.223884+00:00
-- url     : https://prove2.me/submissions/02675932-539e-4537-9164-b1b2bf078dc3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_TenChallenges_Challenge_06
import Theorems.Thm_TenChallenges_challenge_06_r2
import Theorems.Thm_TenChallenges_isAlphaWQO_mono

open TenChallenges in
theorem solution : TenChallenges.statement_06 0 := by
  have h2 := challenge_06_r2
  unfold TenChallenges.statement_06 at h2 ⊢
  have hmod : (2 : Ordinal) % 2 = 0 := Ordinal.mod_self 2
  have hdiv : (2 : Ordinal) / 2 = 1 := Ordinal.div_self two_ne_zero
  rw [if_pos hmod, hdiv] at h2
  rw [if_pos (Ordinal.zero_mod 2), Ordinal.zero_div]
  exact isAlphaWQO_mono PlanarGraph.MinorLE zero_le_one h2
