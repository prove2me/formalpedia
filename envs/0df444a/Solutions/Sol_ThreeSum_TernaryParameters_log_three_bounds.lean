-- Prove2me | solution 1 for ThreeSum.TernaryParameters.log_three_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:40.137826+00:00
-- url     : https://prove2.me/submissions/78290aa8-a4a0-4cef-86d4-1262a0e1c85a

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
noncomputable section
namespace ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
private theorem log_two_bounds :
    (13862943611198906187 / 20000000000000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (17328679513998632737 / 25000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1 / 3 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) : ℝ) = 2 := by
    norm_num []
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
private theorem log_normalized_three_bounds :
    (40546510810816438197 / 100000000000000000000 : ℝ) ≤ Real.log normalized_three ∧ Real.log normalized_three ≤ (20273255405408219099 / 50000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1 / 5 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (1 / 5 : ℝ)) / (1 - (1 / 5 : ℝ)) : ℝ) = normalized_three := by
    norm_num [normalized_three]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
end ThreeSum.TernaryParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution :
    (27465307216702742283 / 25000000000000000000 : ℝ) ≤ Real.log three ∧ Real.log three ≤ (54930614433405484573 / 50000000000000000000 : ℝ) := by
  have hu := log_normalized_three_bounds
  have htwo := log_two_bounds
  have heq : three = normalized_three * (2 : ℝ) ^ 1 := by norm_num [three, normalized_three]
  rw [heq, Real.log_mul (by norm_num [normalized_three]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]
end ThreeSum.TernaryParameters
