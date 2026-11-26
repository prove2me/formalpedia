-- Prove2me | solution 1 for circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:43.377152+00:00
-- url     : https://prove2.me/submissions/858b359c-3335-4467-a841-cc91e174fd0d

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_circleIntegral_resolvent_eq_of_spectrum_subset_ball
import Theorems.Thm_circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    circleIntegral (resolvent A) c r = (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  have hR : ‖A - c • (1 : E →L[ℂ] E)‖ < ‖A - c • (1 : E →L[ℂ] E)‖ + r := by linarith
  rw [circleIntegral_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg (A - c • (1 : E →L[ℂ] E))] :
      r ≤ ‖A - c • (1 : E →L[ℂ] E)‖ + r) hσ]
  exact circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt A c hR
