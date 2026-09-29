-- Prove2me | solution 1 for TarchaBraids.thm_3_15_half_twists_adjacent_braid_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T13:37:39.480456+00:00
-- url     : https://prove2.me/submissions/6d376983-f9df-4e3f-9288-f454f55d1241

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_quotient_eq_v1

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) :
    ∀ i j : Fin (n - 1), (j : ℕ) = (i : ℕ) + 1 →
      halfTwistBraid n i * halfTwistBraid n j * halfTwistBraid n i =
        halfTwistBraid n j * halfTwistBraid n i * halfTwistBraid n j := by
  intro i j hji
  rw [FundamentalGroup.mul_def, FundamentalGroup.mul_def,
    FundamentalGroup.mul_def, FundamentalGroup.mul_def]
  change Path.Homotopic.Quotient.mk (leftBraidWordLoop n i j) =
    Path.Homotopic.Quotient.mk (rightBraidWordLoop n i j)
  exact TarchaBraids.thm_3_15_adjacent_word_quotient_eq_v1 i j hji
