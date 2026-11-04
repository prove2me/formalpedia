-- Prove2me | solution 1 for ThreeSum.TernaryParameters.log_alpha0_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:58.03571+00:00
-- url     : https://prove2.me/submissions/b5bb2e27-bb2e-4792-b9b7-00326b572c1f

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
private theorem log_normalized_alpha0_bounds :
    (58904408512896013021 / 100000000000000000000 : ℝ) ≤ Real.log normalized_alpha0 ∧ Real.log normalized_alpha0 ≤ (29452204256448006511 / 50000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((40113239 / 140113239 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (40113239 / 140113239 : ℝ)) / (1 - (40113239 / 140113239 : ℝ)) : ℝ) = normalized_alpha0 := by
    norm_num [normalized_alpha0]
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
    (-10410309543098517927 / 100000000000000000000 : ℝ) ≤ Real.log alpha0 ∧ Real.log alpha0 ≤ (-10410309543098517913 / 100000000000000000000 : ℝ) := by
  have hu := log_normalized_alpha0_bounds
  have htwo := log_two_bounds
  have heq : alpha0 = normalized_alpha0 / (2 : ℝ) ^ 1 := by norm_num [alpha0, normalized_alpha0]
  rw [heq, Real.log_div (by norm_num [normalized_alpha0]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]
end ThreeSum.TernaryParameters
