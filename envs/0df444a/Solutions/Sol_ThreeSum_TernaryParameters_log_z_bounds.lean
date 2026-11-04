-- Prove2me | solution 1 for ThreeSum.TernaryParameters.log_z_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:42.548382+00:00
-- url     : https://prove2.me/submissions/22156eaf-d430-4857-ade9-f7a4fe21cb7d

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
private theorem log_normalized_z_bounds :
    (18551336023222543863 / 100000000000000000000 : ℝ) ≤ Real.log normalized_z ∧ Real.log normalized_z ≤ (2318917002902817983 / 12500000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((127397677 / 1377397677 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (127397677 / 1377397677 : ℝ)) / (1 - (127397677 / 1377397677 : ℝ)) : ℝ) = normalized_z := by
    norm_num [normalized_z]
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
    (-258707536200755579929 / 100000000000000000000 : ℝ) ≤ Real.log z ∧ Real.log z ≤ (-64676884050188894969 / 25000000000000000000 : ℝ) := by
  have hu := log_normalized_z_bounds
  have htwo := log_two_bounds
  have heq : z = normalized_z / (2 : ℝ) ^ 4 := by norm_num [z, normalized_z]
  rw [heq, Real.log_div (by norm_num [normalized_z]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]
end ThreeSum.TernaryParameters
