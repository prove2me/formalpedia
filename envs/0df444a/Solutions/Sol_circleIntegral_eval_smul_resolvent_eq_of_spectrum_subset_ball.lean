-- Prove2me | solution 1 for circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:39.042718+00:00
-- url     : https://prove2.me/submissions/9b8a598e-61d6-426b-a931-f9acf99b1170

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_mem_resolventSet_of_notMem_ball_of_spectrum_subset
import Theorems.Thm_differentiableAt_eval_smul_resolvent

set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {c : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hσ : spectrum ℂ A ⊆ Metric.ball c r) (p : ℂ[X]) :
    circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c r =
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c R := by
  refine (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    (s := ∅) Set.countable_empty ?_ ?_).symm
  · intro z hz
    exact (differentiableAt_eval_smul_resolvent A p
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ hz.2)).continuousAt.continuousWithinAt
  · intro z hz
    refine differentiableAt_eval_smul_resolvent A p
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ ?_)
    intro hzr
    exact hz.1.2 (Metric.ball_subset_closedBall hzr)
