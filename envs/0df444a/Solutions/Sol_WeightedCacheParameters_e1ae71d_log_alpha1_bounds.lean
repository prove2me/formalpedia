-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.log_alpha1_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:37.150089+00:00
-- url     : https://prove2.me/submissions/c05a2c1a-80ec-45aa-8b9a-2d1bba199235

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
noncomputable section
namespace WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
private theorem log_two_raw :
    (693147180559945309 / 1000000000000000000 : ℝ) ≤ Real.log (2 / 1 : ℝ) ∧ Real.log (2 / 1 : ℝ) ≤ (69314718055994531 / 100000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(1 / 3 : ℝ)| < 1) 20
  have heq : (1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) = (2 / 1 : ℝ) := by norm_num
  rw [heq] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
private theorem log_alpha1_raw :
    (354479189003227673 / 1000000000000000000 : ℝ) ≤ Real.log (5568117488677 / 3906250000000 : ℝ) ∧ Real.log (5568117488677 / 3906250000000 : ℝ) ≤ (177239594501613837 / 500000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(1661867488677 / 9474367488677 : ℝ)| < 1) 20
  have heq : (1 + (1661867488677 / 9474367488677 : ℝ)) / (1 - (1661867488677 / 9474367488677 : ℝ)) = (5568117488677 / 3906250000000 : ℝ) := by norm_num
  rw [heq] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
end WeightedCacheParameters_e1ae71d
set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution :
    (-2418109533236553567 / 1000000000000000000 : ℝ) ≤ Real.log (alpha1) ∧ Real.log (alpha1) ≤ (-2418109533236553561 / 1000000000000000000 : ℝ) := by
  have h := log_alpha1_raw
  have ht := log_two_raw
  have heq : (alpha1) = (5568117488677 / 3906250000000 : ℝ) / (2 : ℝ) ^ 4 := by norm_num [alpha1]
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters_e1ae71d
