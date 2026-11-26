-- Prove2me | solution 1 for circleIntegral_resolvent_eq_of_spectrum_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:19:37.921271+00:00
-- url     : https://prove2.me/submissions/c2324915-b38c-49a4-8b54-4463e8fd8430

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_mem_resolventSet_of_notMem_ball_of_spectrum_subset

set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {c : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    circleIntegral (resolvent A) c r = circleIntegral (resolvent A) c R := by
  refine (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    (s := ∅) Set.countable_empty ?_ ?_).symm
  · intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ hz.2)).continuousAt.continuousWithinAt
  · intro z hz
    refine (spectrum.hasDerivAt_resolvent_const_left
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ ?_)).differentiableAt
    intro hzr
    exact hz.1.2 (Metric.ball_subset_closedBall hzr)
