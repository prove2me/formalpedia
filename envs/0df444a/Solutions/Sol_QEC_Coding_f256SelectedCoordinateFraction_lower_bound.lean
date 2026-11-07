-- Prove2me | solution 1 for QEC.Coding.f256SelectedCoordinateFraction_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:53:35.337948+00:00
-- url     : https://prove2.me/submissions/976509e3-4c7c-4d4f-a15c-b39891c7d232

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Theorems.Thm_QEC_Coding_f256SelectedCoordinates_card_ge_one
set_option autoImplicit false
open QEC QEC.Coding
theorem solution : (1 : ℚ) / 512 ≤ f256SelectedCoordinateFraction := by
  rw [f256SelectedCoordinateFraction]
  have hcard : (1 : ℚ) ≤ f256SelectedCoordinates.card := by
    exact_mod_cast f256SelectedCoordinates_card_ge_one
  nlinarith
