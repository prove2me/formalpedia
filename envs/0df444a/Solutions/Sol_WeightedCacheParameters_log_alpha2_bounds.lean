-- Prove2me | solution 1 for WeightedCacheParameters.log_alpha2_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:01:13.248675+00:00
-- url     : https://prove2.me/submissions/c708af9d-3271-4593-88e0-82f795bed6da

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
noncomputable section
namespace WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
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
    (13899050664788809 / 62500000000000000 : ℝ) ≤ Real.log (292746547 / 234375000 : ℝ) ∧ Real.log (292746547 / 234375000 : ℝ) ≤ (44476962127324189 / 200000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(58371547 / 527121547 : ℝ)| < 1) 20
  have heq : (1 + (58371547 / 527121547 : ℝ)) / (1 - (58371547 / 527121547 : ℝ)) = (292746547 / 234375000 : ℝ) := by norm_num
  rw [heq] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
end WeightedCacheParameters
set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution :
    (-2314822726641498113 / 500000000000000000 : ℝ) ≤ Real.log (alpha2) ∧ Real.log (alpha2) ≤ (-4629645453282996217 / 1000000000000000000 : ℝ) := by
  have h := log_alpha2_raw
  have ht := log_two_raw
  have heq : (alpha2) = (292746547 / 234375000 : ℝ) / (2 : ℝ) ^ 7 := by norm_num [alpha2]
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters
