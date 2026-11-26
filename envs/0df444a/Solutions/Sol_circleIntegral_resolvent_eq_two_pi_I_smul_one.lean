-- Prove2me | solution 1 for circleIntegral_resolvent_eq_two_pi_I_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:42.458184+00:00
-- url     : https://prove2.me/submissions/57afddd2-d87f-4837-b9f4-fad467ad2a5c

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Theorems.Thm_normalized_circleIntegral_resolvent_eq_one

set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) :
    circleIntegral (resolvent A) 0 R =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  have h := congrArg (fun T : E →L[ℂ] E => (2 * (Real.pi : ℂ) * I) • T)
    (normalized_circleIntegral_resolvent_eq_one A hR)
  have hscalar : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  simpa only [smul_smul, mul_inv_cancel₀ hscalar, one_smul] using h
