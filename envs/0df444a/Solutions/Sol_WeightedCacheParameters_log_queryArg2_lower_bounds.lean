-- Prove2me | solution 1 for WeightedCacheParameters.log_queryArg2_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:02:05.973831+00:00
-- url     : https://prove2.me/submissions/694ab42f-92b5-4057-9dc6-ff27bf6e8256

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
private theorem log_queryArg2_lower_raw :
    (15493328653985123 / 200000000000000000 : ℝ) ≤ Real.log (540273094184934183 / 500000000000000000 : ℝ) ∧ Real.log (540273094184934183 / 500000000000000000 : ℝ) ≤ (4841665204370351 / 62500000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(40273094184934183 / 1040273094184934183 : ℝ)| < 1) 20
  have heq : (1 + (40273094184934183 / 1040273094184934183 : ℝ)) / (1 - (40273094184934183 / 1040273094184934183 : ℝ)) = (540273094184934183 / 500000000000000000 : ℝ) := by norm_num
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
    (15493328653985123 / 200000000000000000 : ℝ) ≤ Real.log ((540273094184934183 / 500000000000000000 : ℝ)) ∧ Real.log ((540273094184934183 / 500000000000000000 : ℝ)) ≤ (77466643269925617 / 1000000000000000000 : ℝ) := by
  have h := log_queryArg2_lower_raw
  have ht := log_two_raw
  have heq : ((540273094184934183 / 500000000000000000 : ℝ)) = (540273094184934183 / 500000000000000000 : ℝ) / (2 : ℝ) ^ 0 := by norm_num []
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters
