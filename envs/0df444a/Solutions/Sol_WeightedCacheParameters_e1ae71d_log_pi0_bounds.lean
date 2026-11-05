-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.log_pi0_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:07.785542+00:00
-- url     : https://prove2.me/submissions/5c6fff97-1282-4b6f-9d4f-66e68fd87cce

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
private theorem log_pi0_raw :
    (947189631449907 / 1953125000000000 : ℝ) ≤ Real.log (406027953884819 / 250000000000000 : ℝ) ∧ Real.log (406027953884819 / 250000000000000 : ℝ) ≤ (96992218260470477 / 200000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |(156027953884819 / 656027953884819 : ℝ)| < 1) 20
  have heq : (1 + (156027953884819 / 656027953884819 : ℝ)) / (1 - (156027953884819 / 656027953884819 : ℝ)) = (406027953884819 / 250000000000000 : ℝ) := by norm_num
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
    (-104093044628796463 / 500000000000000000 : ℝ) ≤ Real.log (pi0) ∧ Real.log (pi0) ≤ (-208186089257592923 / 1000000000000000000 : ℝ) := by
  have h := log_pi0_raw
  have ht := log_two_raw
  have heq : (pi0) = (406027953884819 / 250000000000000 : ℝ) / (2 : ℝ) ^ 1 := by norm_num [pi0]
  rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]
end WeightedCacheParameters_e1ae71d
