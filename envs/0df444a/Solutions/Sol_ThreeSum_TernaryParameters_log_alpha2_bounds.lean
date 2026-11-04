-- Prove2me | solution 1 for ThreeSum.TernaryParameters.log_alpha2_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:26.466746+00:00
-- url     : https://prove2.me/submissions/98dc1f1b-a3b9-4e6c-8541-39c637f20181

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
private theorem log_normalized_alpha2_bounds :
    (17569410943365283 / 78125000000000000 : ℝ) ≤ Real.log normalized_alpha2 ∧ Real.log normalized_alpha2 ≤ (22488846007507562241 / 100000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((98509 / 879759 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (98509 / 879759 : ℝ)) / (1 - (98509 / 879759 : ℝ)) : ℝ) = normalized_alpha2 := by
    norm_num [normalized_alpha2]
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
    (-115678545096113538599 / 25000000000000000000 : ℝ) ≤ Real.log alpha2 ∧ Real.log alpha2 ≤ (-7229909068507096161 / 1562500000000000000 : ℝ) := by
  have hu := log_normalized_alpha2_bounds
  have htwo := log_two_bounds
  have heq : alpha2 = normalized_alpha2 / (2 : ℝ) ^ 7 := by norm_num [alpha2, normalized_alpha2]
  rw [heq, Real.log_div (by norm_num [normalized_alpha2]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]
end ThreeSum.TernaryParameters
