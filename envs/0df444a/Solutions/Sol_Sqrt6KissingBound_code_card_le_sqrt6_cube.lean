-- Prove2me | solution 1 for Sqrt6KissingBound.code_card_le_sqrt6_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:30:41.368905+00:00
-- url     : https://prove2.me/submissions/dd0004be-51c6-4f28-8ffc-39363aec1f26

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Theorems.Thm_Sqrt6KissingBound_code_card_le_fourteen_dim_three

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution
    (X : Finset (EuclideanSpace ℝ (Fin 3)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ 3 := by
  have hc : (X.card : ℝ) ≤ 14 := by
    exact_mod_cast code_card_le_fourteen_dim_three X hunit hsep
  have hs0 := Real.sqrt_nonneg (6 : ℝ)
  have hs2 : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  have hs : (7 : ℝ) / 3 < Real.sqrt 6 := by nlinarith
  have hs3 : (Real.sqrt 6) ^ 3 = 6 * Real.sqrt 6 := by
    rw [pow_succ, hs2]
  rw [hs3]
  nlinarith
end Sqrt6KissingBound
