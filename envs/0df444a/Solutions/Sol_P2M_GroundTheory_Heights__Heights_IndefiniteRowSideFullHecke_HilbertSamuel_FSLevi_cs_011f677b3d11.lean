-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_cs_011f677b3d11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:44.758492+00:00
-- url     : https://prove2.me/submissions/d30d9f23-75c0-45a1-a9b2-eaa38fe2e9cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_reP_apply_7da478929125
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_imaginaryPart_apply_dff8249560c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_FSLevi_norm_sq_eq_73ea6bfcdf63

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
theorem _root_.solution (z w : J → ℂ) :
    (∑ p, (reP p z * reP p w + imaginary p z * imaginary p w)) ^ 2 +
      (∑ p, (reP p z * reP p (Complex.I • w) + imaginary p z * imaginary p (Complex.I • w))) ^ 2 ≤
      nsq z * nsq w := by
  set a : J → ℂ := fun p ↦ starRingEnd ℂ (z p) * w p
  have h1 : (∑ p, (reP p z * reP p w + imaginary p z * imaginary p w)) = (∑ p, a p).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [a, reP_apply, imaginaryPart_apply, Complex.mul_re]
  have h2 : (∑ p, (reP p z * reP p (Complex.I • w) + imaginary p z * imaginary p (Complex.I • w))) =
      -(∑ p, a p).im := by
    rw [Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [a, reP_apply, imaginaryPart_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [h1, h2, neg_sq]
  have h3 : (∑ p, a p).re ^ 2 + (∑ p, a p).im ^ 2 = ‖∑ p, a p‖ ^ 2 := (norm_sq_eq _).symm
  rw [h3]
  have h4 : ‖∑ p, a p‖ ≤ ∑ p, ‖z p‖ * ‖w p‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [a]
  have h5 : (∑ p, ‖z p‖ * ‖w p‖) ^ 2 ≤ nsq z * nsq w := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p ↦ ‖z p‖) (fun p ↦ ‖w p‖)
    simpa [nsq, reP_apply, imaginaryPart_apply, norm_sq_eq] using this
  calc ‖∑ p, a p‖ ^ 2 ≤ (∑ p, ‖z p‖ * ‖w p‖) ^ 2 := by gcongr
    _ ≤ nsq z * nsq w := h5
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.FSLevi
