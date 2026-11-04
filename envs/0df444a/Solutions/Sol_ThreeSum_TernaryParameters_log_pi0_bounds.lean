-- Prove2me | solution 1 for ThreeSum.TernaryParameters.log_pi0_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:15.12518+00:00
-- url     : https://prove2.me/submissions/de4734fd-2693-4d04-a659-b321c6400fcb

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
private theorem log_normalized_pi0_bounds :
    (6061883603841429449 / 12500000000000000000 : ℝ) ≤ Real.log normalized_pi0 ∧ Real.log normalized_pi0 ≤ (48495068830731435593 / 100000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((15602373 / 65602373 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (15602373 / 65602373 : ℝ)) / (1 - (15602373 / 65602373 : ℝ)) : ℝ) = normalized_pi0 := by
    norm_num [normalized_pi0]
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
    (-5204912306315773839 / 25000000000000000000 : ℝ) ≤ Real.log pi0 ∧ Real.log pi0 ≤ (-10409824612631547671 / 50000000000000000000 : ℝ) := by
  have hu := log_normalized_pi0_bounds
  have htwo := log_two_bounds
  have heq : pi0 = normalized_pi0 / (2 : ℝ) ^ 1 := by norm_num [pi0, normalized_pi0]
  rw [heq, Real.log_div (by norm_num [normalized_pi0]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]
end ThreeSum.TernaryParameters
