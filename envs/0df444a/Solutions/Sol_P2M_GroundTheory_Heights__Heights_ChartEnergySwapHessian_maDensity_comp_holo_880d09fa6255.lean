-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_maDensity_comp_holo_880d09fa6255
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:15.186028+00:00
-- url     : https://prove2.me/submissions/31aa7799-994c-4239-9125-780bdb3e185f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_comp_holo_687153abf862
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mixedDisc_mul_mul_6e0de3118a6e


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
theorem _root_.solution (Φ' Φ : Fin D → (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ))
    (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ) (hΦ : ∀ j, ContDiffAt ℝ 2 (Φ j) (F y)) (hF : ContDiffAt ℂ 2 F y)
    (hh : ContDiffAt ℂ 2 h y) (hΦ' : ∀ j, Φ' j =ᶠ[𝓝 y] fun y' => Φ j (F y') + (h y').re) :
    maDensity Φ' y = Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det *
      maDensity Φ (F y) := by
  set J := LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) with hJ
  have hQ : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
  have hH : ∀ j, cxHessian (Φ' j) y = Jᵀ * cxHessian (Φ j) (F y) * J.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_holo (Φ' j) (Φ j) F h y (hΦ j) hF hh (hΦ' j)
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Jᵀ) (J.map (starRingEnd ℂ)) (fun j => cxHessian (Φ j) (F y)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
