-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_of_form_cb255067719c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:06:47.408817+00:00
-- url     : https://prove2.me/submissions/4d331c55-32e3-42f3-b2f7-43e2d30b0c70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_sesq_eq_of_form_c6b7ddfb0652
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_eq_sesq_4253c4c2c89e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_expand_69b1d82df637


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
open ChartMongeAmpereAffineInvariance
variable {D : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E']
namespace GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
theorem _root_.solution (f g : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ))
    (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, fderiv ℝ (fderiv ℝ f) y u v = fderiv ℝ (fderiv ℝ g) w (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) :
    cxHessian f y = (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ * cxHessian g w *
      (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map (starRingEnd ℂ) := by
  ext i j
  rw [cxHessian_eq_sesq, sesq_eq_of_form _ _ L R hH hR₁ hR₂, sesq_expand]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hc : cxHessian g w l k = sesq (fderiv ℝ (fderiv ℝ g) w) (Pi.single l 1) (Pi.single k 1) := rfl
  simp only [hc, starRingEnd_apply]
  ring
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
