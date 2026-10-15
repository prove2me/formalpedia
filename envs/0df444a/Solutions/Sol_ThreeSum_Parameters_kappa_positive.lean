-- Prove2me | solution 1 for ThreeSum.Parameters.kappa_positive
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:00:28.319085+00:00
-- url     : https://prove2.me/submissions/7ae4222e-1adc-47f5-879b-f578ea7f63fe

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Analytic and rational parameter certificate for the proposed 3SUM algorithm

This module certifies the real-variable inequalities and the resulting exponent ledger.
It does not by itself prove that an implementation has those costs: the reduction,
cover, encoding, reporting, arithmetic and machine-model lemmas are separate obligations.

All decimal-looking constants below are exact rational numbers. There are no numerical
oracles, admitted declarations, or native-code decision procedures in this certificate.
-/

noncomputable section

namespace ThreeSum.Parameters

open Set Real

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048







































/-! ## Exact integer witnesses for the logarithmic comparisons -/





































private theorem log_512 : Real.log 512 = 9 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 9
  norm_num at h
  exact h































theorem kappa_formula :
    kappa * Real.log 2 =
      256 * Real.log (512 / 511) + 255 * Real.log (510 / 511) := by
  have h510 : Real.log (510 : ℝ) = Real.log 2 + Real.log 255 := by
    rw [show (510 : ℝ) = 2 * 255 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [kappa, entropy, Real.binEntropy]
  rw [Real.log_div (by norm_num : (512 : ℝ) ≠ 0) (by norm_num : (511 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (256 : ℝ) ≠ 0) (by norm_num : (255 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (510 : ℝ) ≠ 0) (by norm_num : (511 : ℝ) ≠ 0),
    log_256, log_512, h510]
  field_simp
  ring












theorem kappa_positive_sourceProof : 0 < kappa := by
  have hp := (abs_le.mp (Real.sum_range_sub_log_div_le
    (by norm_num : |(1 / 1023 : ℝ)| < 1) 1)).1
  have hm := (abs_le.mp (Real.sum_range_sub_log_div_le
    (by norm_num : |(-(1 / 1021) : ℝ)| < 1) 1)).1
  norm_num [Finset.sum_range_succ] at hp hm
  have hnum : (1 / 1023 : ℝ) ≤ kappa * Real.log 2 := by
    rw [kappa_formula]
    linarith
  by_contra h
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) log_two_pos.le
  linarith



















































/-! ## Exact rational inequalities for the schedule -/

















































































































































































































































































/-! ## The real-valued ledger, before the algorithmic cost lemmas are applied -/





























































end ThreeSum.Parameters

end
end


theorem solution : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  ThreeSum.Parameters.kappa := by
  exact @ThreeSum.Parameters.kappa_positive_sourceProof

#print axioms solution
