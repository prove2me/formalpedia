-- Prove2me | solution 1 for WeightedCacheParameters.log_pi0_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:01:06.104207+00:00
-- url     : https://prove2.me/submissions/a9ccaafa-6568-4f14-977d-b133cc359912

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
private theorem log_pi0_raw :
    (48496416489187053 / 100000000000000000 : ℝ) ≤ Real.log (8120584037 / 5000000000 : ℝ) ∧ Real.log (8120584037 / 5000000000 : ℝ) ≤ (484964164891870531 / 1000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(3120584037 / 13120584037 : ℝ)| < 1) 20
  have heq : (1 + (3120584037 / 13120584037 : ℝ)) / (1 - (3120584037 / 13120584037 : ℝ)) = (8120584037 / 5000000000 : ℝ) := by norm_num
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
    (-10409150783403739 / 50000000000000000 : ℝ) ≤ Real.log (pi0) ∧ Real.log (pi0) ≤ (-208183015668074777 / 1000000000000000000 : ℝ) := by
  have h := log_pi0_raw
  have ht := log_two_raw
  have heq : (pi0) = (8120584037 / 5000000000 : ℝ) / (2 : ℝ) ^ 1 := by norm_num [pi0]
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters
