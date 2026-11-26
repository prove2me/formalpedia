-- Prove2me | solution 1 for circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:44.517122+00:00
-- url     : https://prove2.me/submissions/dc6f051f-602f-451d-a7ce-85b6bd612b5d

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_circleIntegral_resolvent_eq_of_spectrum_subset_ball
import Theorems.Thm_circleIntegral_resolvent_eq_two_pi_I_smul_one


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) :
    circleIntegral (resolvent A) 0 r = (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  have hR : ‖A‖ < ‖A‖ + r := by linarith
  rw [circleIntegral_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg A] : r ≤ ‖A‖ + r) hσ]
  exact circleIntegral_resolvent_eq_two_pi_I_smul_one A hR
