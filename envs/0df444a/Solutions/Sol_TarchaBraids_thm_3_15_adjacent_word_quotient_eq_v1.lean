-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_word_quotient_eq_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T13:33:33.003163+00:00
-- url     : https://prove2.me/submissions/c0358118-fcf3-4225-bdee-044256e88d1a

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1
import Theorems.Thm_TarchaBraids_thm_3_15_left_word_eq_outer_quotient_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_word_eq_outer_quotient_v1

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      Path.Homotopic.Quotient.mk (leftBraidWordLoop n i j) =
        Path.Homotopic.Quotient.mk (rightBraidWordLoop n i j) := by
  intro n i j hji
  exact
    (TarchaBraids.thm_3_15_left_word_eq_outer_quotient_v1 i j hji).trans
      (TarchaBraids.thm_3_15_right_word_eq_outer_quotient_v1 i j hji).symm
