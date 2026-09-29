-- Prove2me | solution 1 for TarchaBraids.thm_3_15_right_word_eq_outer_quotient_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T13:28:58.168542+00:00
-- url     : https://prove2.me/submissions/01e58c18-d2c8-43ca-8147-28fe5f137704

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1
import Definitions.Def_TarchaBraids_adjacent_outer_loop_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_word_homotopic_outer_v1

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      Path.Homotopic.Quotient.mk (rightBraidWordLoop n i j) =
        Path.Homotopic.Quotient.mk (outerRotateLoop i j hji) := by
  intro n i j hji
  exact (Path.Homotopic.Quotient.eq).2
    (TarchaBraids.thm_3_15_right_word_homotopic_outer_v1 i j hji)
