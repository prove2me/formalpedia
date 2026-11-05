-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.log_queryArg2_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:42.51503+00:00
-- url     : https://prove2.me/submissions/d8b84080-66ba-43e1-a6f0-fa8cdb7aef81

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
private theorem log_queryArg2_lower_raw :
    (19387293186940463 / 250000000000000000 : ℝ) ≤ Real.log (540317684481267861 / 500000000000000000 : ℝ) ∧ Real.log (540317684481267861 / 500000000000000000 : ℝ) ≤ (77549172747761853 / 1000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(40317684481267861 / 1040317684481267861 : ℝ)| < 1) 20
  have heq : (1 + (40317684481267861 / 1040317684481267861 : ℝ)) / (1 - (40317684481267861 / 1040317684481267861 : ℝ)) = (540317684481267861 / 500000000000000000 : ℝ) := by norm_num
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
    (19387293186940463 / 250000000000000000 : ℝ) ≤ Real.log ((540317684481267861 / 500000000000000000 : ℝ)) ∧ Real.log ((540317684481267861 / 500000000000000000 : ℝ)) ≤ (38774586373880927 / 500000000000000000 : ℝ) := by
  have h := log_queryArg2_lower_raw
  have ht := log_two_raw
  have heq : ((540317684481267861 / 500000000000000000 : ℝ)) = (540317684481267861 / 500000000000000000 : ℝ) / (2 : ℝ) ^ 0 := by norm_num []
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters_e1ae71d
