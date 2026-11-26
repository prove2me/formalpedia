-- Prove2me | solution 1 for circleIntegral_smul_resolvent_eq_of_spectrum_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:01.180743+00:00
-- url     : https://prove2.me/submissions/28cb5064-f257-4944-887d-2e561d95853a

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
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hσ : spectrum ℂ A ⊆ Metric.ball c r)
    {g : ℂ → ℂ} (hg : ∀ z, z ∉ Metric.ball c r → DifferentiableAt ℂ g z) :
    circleIntegral (fun z : ℂ => g z • resolvent A z) c r =
      circleIntegral (fun z : ℂ => g z • resolvent A z) c R := by
  refine (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    (s := ∅) Set.countable_empty ?_ ?_).symm
  · intro z hz
    exact ((hg z hz.2).smul (spectrum.hasDerivAt_resolvent_const_left
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ hz.2)).differentiableAt
      ).continuousAt.continuousWithinAt
  · intro z hz
    have hz' : z ∉ Metric.ball c r := fun h => hz.1.2 (Metric.ball_subset_closedBall h)
    exact (hg z hz').smul (spectrum.hasDerivAt_resolvent_const_left
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ hz')).differentiableAt
