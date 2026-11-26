-- Prove2me | solution 1 for circleIntegral_eval_smul_resolvent_eq_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:50.246912+00:00
-- url     : https://prove2.me/submissions/de56e554-06f0-4ae0-9e6f-fd74504ed7b2

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_resolvent_sub_smul_one_shift
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) (c : ℂ) (R : ℝ) (p : ℂ[X]) :
    circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c R =
      circleIntegral (fun w : ℂ => (p.affineComposition 1 c).eval w •
        resolvent (A - c • (1 : E →L[ℂ] E)) w) 0 R := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro t _
  have hmap : circleMap c R t = circleMap 0 R t + c := by
    rw [← circleMap_sub_center c R t]
    ring
  have hderiv : deriv (circleMap c R) t = deriv (circleMap 0 R) t := by
    rw [deriv_circleMap, deriv_circleMap]
  simp only [hderiv, hmap, eval_affineComposition, one_mul, resolvent_sub_smul_one_shift]
