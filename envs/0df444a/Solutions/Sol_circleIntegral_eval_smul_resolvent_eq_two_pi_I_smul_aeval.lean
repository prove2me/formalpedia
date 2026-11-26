-- Prove2me | solution 1 for circleIntegral_eval_smul_resolvent_eq_two_pi_I_smul_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:51.421782+00:00
-- url     : https://prove2.me/submissions/a9ba8897-b74f-4b39-9fa4-8dfb2bf69d1c

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval

set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    circleIntegral (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R =
      (2 * (Real.pi : ℂ) * I) • Polynomial.aeval A p := by
  have h := congrArg (fun T : E →L[ℂ] E => (2 * (Real.pi : ℂ) * I) • T)
    (normalized_circleIntegral_eval_smul_resolvent_eq_aeval A hR p)
  have hscalar : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  simpa only [smul_smul, mul_inv_cancel₀ hscalar, one_smul] using h
