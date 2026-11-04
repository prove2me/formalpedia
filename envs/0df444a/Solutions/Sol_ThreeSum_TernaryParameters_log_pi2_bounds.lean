-- Prove2me | solution 1 for ThreeSum.TernaryParameters.log_pi2_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:17.453546+00:00
-- url     : https://prove2.me/submissions/01e5756b-9658-4e4f-b2a9-b41fb26226fa

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
private theorem log_normalized_pi2_bounds :
    (31517678409162000219 / 50000000000000000000 : ℝ) ≤ Real.log normalized_pi2 ∧ Real.log normalized_pi2 ≤ (63035356818324000439 / 100000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((171538 / 562163 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (171538 / 562163 : ℝ)) / (1 - (171538 / 562163 : ℝ)) : ℝ) = normalized_pi2 := by
    norm_num [normalized_pi2]
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
    (-1411411806070572741 / 400000000000000000 : ℝ) ≤ Real.log pi2 ∧ Real.log pi2 ≤ (-352852951517643185171 / 100000000000000000000 : ℝ) := by
  have hu := log_normalized_pi2_bounds
  have htwo := log_two_bounds
  have heq : pi2 = normalized_pi2 / (2 : ℝ) ^ 6 := by norm_num [pi2, normalized_pi2]
  rw [heq, Real.log_div (by norm_num [normalized_pi2]) (by norm_num),
    Real.log_pow]
  norm_num
  constructor <;> linarith [hu.1, hu.2, htwo.1, htwo.2]
end ThreeSum.TernaryParameters
