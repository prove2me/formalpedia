-- Prove2me | solution 1 for Sqrt6KissingBound.sqrt6_le_of_isUniversalKissingBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:33:27.049425+00:00
-- url     : https://prove2.me/submissions/346fecec-f173-426f-a223-ccbdaa201c1c

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_regularHexagon_card
import Theorems.Thm_Sqrt6KissingBound_regularHexagon_isKissingConfiguration
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {α : ℝ}
    (hα : IsUniversalKissingBase α) : Real.sqrt 6 ≤ α := by
  have h6 : (6 : ℝ) ≤ α ^ 2 := by
    have h := hα.2 (n := 2) (by norm_num) regularHexagon
      regularHexagon_isKissingConfiguration
    simpa [regularHexagon_card] using h
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  nlinarith [hα.1]
end Sqrt6KissingBound
