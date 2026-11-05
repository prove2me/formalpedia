-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.log_alpha2_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:37.785246+00:00
-- url     : https://prove2.me/submissions/449ec084-ed1d-4a2d-8f01-5ef0aa523a4a

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
private theorem log_alpha2_raw :
    (55752800012110641 / 250000000000000000 : ℝ) ≤ Real.log (4882166296349 / 3906250000000 : ℝ) ∧ Real.log (4882166296349 / 3906250000000 : ℝ) ≤ (44602240009688513 / 200000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(975916296349 / 8788416296349 : ℝ)| < 1) 20
  have heq : (1 + (975916296349 / 8788416296349 : ℝ)) / (1 - (975916296349 / 8788416296349 : ℝ)) = (4882166296349 / 3906250000000 : ℝ) := by norm_num
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
    (-2314509531935587303 / 500000000000000000 : ℝ) ≤ Real.log (alpha2) ∧ Real.log (alpha2) ≤ (-4629019063871174597 / 1000000000000000000 : ℝ) := by
  have h := log_alpha2_raw
  have ht := log_two_raw
  have heq : (alpha2) = (4882166296349 / 3906250000000 : ℝ) / (2 : ℝ) ^ 7 := by norm_num [alpha2]
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters_e1ae71d
