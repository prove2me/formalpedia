-- Prove2me | solution 1 for circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:55.728064+00:00
-- url     : https://prove2.me/submissions/7be79431-70a3-4827-b43a-5a4242ab31de

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Theorems.Thm_circleIntegral_resolvent_eq_two_pi_I_smul_one
import Theorems.Thm_resolvent_sub_smul_one_shift

set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hR : ‖A - c • (1 : E →L[ℂ] E)‖ < R) :
    circleIntegral (resolvent A) c R =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  let B := A - c • (1 : E →L[ℂ] E)
  have hcenter : circleIntegral (resolvent A) c R = circleIntegral (resolvent B) 0 R := by
    unfold circleIntegral
    apply intervalIntegral.integral_congr
    intro t _
    have hmap : circleMap c R t = circleMap 0 R t + c := by
      rw [← circleMap_sub_center c R t]
      ring
    have hderiv : deriv (circleMap c R) t = deriv (circleMap 0 R) t := by
      rw [deriv_circleMap, deriv_circleMap]
    change deriv (circleMap c R) t • resolvent A (circleMap c R t) =
      deriv (circleMap 0 R) t • resolvent B (circleMap 0 R t)
    rw [hderiv]
    congr 1
    rw [show resolvent A (circleMap c R t) = resolvent B (circleMap 0 R t) by
      rw [hmap]
      exact (resolvent_sub_smul_one_shift A c (circleMap 0 R t)).symm]
  rw [hcenter]
  exact circleIntegral_resolvent_eq_two_pi_I_smul_one B hR
