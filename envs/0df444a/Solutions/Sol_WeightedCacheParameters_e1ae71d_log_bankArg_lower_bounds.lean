-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.log_bankArg_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:08.510639+00:00
-- url     : https://prove2.me/submissions/5f6c5da2-e698-4017-991a-b0a4bc837276

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
private theorem log_bankArg_lower_raw :
    (194416086704412431 / 1000000000000000000 : ℝ) ≤ Real.log (242920311477828953 / 200000000000000000 : ℝ) ∧ Real.log (242920311477828953 / 200000000000000000 : ℝ) ≤ (12151005419025777 / 62500000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(42920311477828953 / 442920311477828953 : ℝ)| < 1) 20
  have heq : (1 + (42920311477828953 / 442920311477828953 : ℝ)) / (1 - (42920311477828953 / 442920311477828953 : ℝ)) = (242920311477828953 / 200000000000000000 : ℝ) := by norm_num
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
    (194416086704412431 / 1000000000000000000 : ℝ) ≤ Real.log ((242920311477828953 / 200000000000000000 : ℝ)) ∧ Real.log ((242920311477828953 / 200000000000000000 : ℝ)) ≤ (194416086704412433 / 1000000000000000000 : ℝ) := by
  have h := log_bankArg_lower_raw
  have ht := log_two_raw
  have heq : ((242920311477828953 / 200000000000000000 : ℝ)) = (242920311477828953 / 200000000000000000 : ℝ) / (2 : ℝ) ^ 0 := by norm_num []
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters_e1ae71d
