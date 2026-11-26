-- Prove2me | solution 1 for Sqrt6KissingBound.upperProfile3_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:21:57.363128+00:00
-- url     : https://prove2.me/submissions/6ea6b797-3a0c-4b5c-ab23-358e338fa6f1

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Theorems.Thm_Sqrt6KissingBound_upperProfile3_sq
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
private lemma s3_pos : 0 < s3_d3 := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq : s3_d3 ^ 2 = 3 := by norm_num [s3_d3]
private lemma a_nonneg : 0 ≤ a_d3 := by positivity
private lemma a_le_one : a_d3 ≤ 1 := by
  dsimp [a_d3]
  nlinarith [s3_sq, s3_pos]
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution :
    (∫ t in a_d3..1, upperProfile3 t ^ 2) = (2 : ℝ) / 3 - 3 * s3_d3 / 8 := by
  calc
    (∫ t in a_d3..1, upperProfile3 t ^ 2) = ∫ t in a_d3..1, (1 - t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc a_d3 1 := by simpa only [Set.uIcc_of_le a_le_one] using ht
      exact upperProfile3_sq (a_nonneg.trans ht'.1) ht'.2
    _ = (2 : ℝ) / 3 - 3 * s3_d3 / 8 := by
      have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a_d3 1 :=
        continuous_const.intervalIntegrable _ _
      have hpow : IntervalIntegrable (fun t : ℝ => t ^ 2) volume a_d3 1 :=
        (continuous_id.pow 2).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hconst hpow,
        intervalIntegral.integral_const, integral_pow]
      norm_num [a_d3, smul_eq_mul]
      linear_combination (s3_d3 / 24) * s3_sq
end Sqrt6KissingBound
