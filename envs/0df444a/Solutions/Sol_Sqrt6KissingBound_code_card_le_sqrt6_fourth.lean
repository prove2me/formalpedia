-- Prove2me | solution 1 for Sqrt6KissingBound.code_card_le_sqrt6_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:31:28.578126+00:00
-- url     : https://prove2.me/submissions/48898f52-8b63-49b5-a0de-a819328b4d2e

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_code_card_le_thirtysix_dim_four

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution
    (X : Finset (EuclideanSpace ℝ (Fin 4)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ 4 := by
  have hc : (X.card : ℝ) ≤ 36 := by exact_mod_cast code_card_le_thirtysix_dim_four X hunit hsep
  have hs : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  calc
    (X.card : ℝ) ≤ 36 := hc
    _ = (Real.sqrt 6) ^ 4 := by
      rw [show (Real.sqrt 6) ^ 4 = ((Real.sqrt 6) ^ 2) ^ 2 by ring, hs]
      norm_num
end Sqrt6KissingBound
