-- Prove2me | solution 1 for ThreeSum.Parameters.kappa_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:12.584817+00:00
-- url     : https://prove2.me/submissions/bb272c53-3625-41ae-b7d2-ca731f2ab309

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_Parameters_log_two_lower
import Theorems.Thm_ThreeSum_Parameters_log_ratio_upper_one
import Theorems.Thm_ThreeSum_Parameters_kappa_formula

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution : kappa < kappaCap := by
  have hp := log_ratio_upper_one (x := (1 / 1023 : ℝ)) (by norm_num)
  have hm := log_ratio_upper_one (x := -(1 / 1021 : ℝ)) (by norm_num)
  norm_num at hp hm
  have hnum : kappa * Real.log 2 ≤ (1 / 1021 : ℝ) := by
    rw [kappa_formula]
    linarith
  have hsmall : kappa * Real.log 2 < (3 / 2000) * Real.log 2 := by
    linarith [log_two_lower]
  exact (mul_lt_mul_iff_of_pos_right log_two_pos).mp hsmall
end ThreeSum.Parameters
