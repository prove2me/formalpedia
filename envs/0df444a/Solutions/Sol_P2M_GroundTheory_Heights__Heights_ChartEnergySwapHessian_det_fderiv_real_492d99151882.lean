-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_det_fderiv_real_492d99151882
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:37.335798+00:00
-- url     : https://prove2.me/submissions/c818fc3d-f1e4-4fcf-aee2-052a80d706aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo

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
theorem _root_.solution {F : (Fin D → ℂ) → (Fin D → ℂ)} {y : Fin D → ℂ} (hF : DifferentiableAt ℂ F y) :
    (fderiv ℝ F y).det =
      Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det := by
  rw [hF.fderiv_restrictScalars ℝ, LinearMap.det_toMatrix']
  have : ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F y) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) :
      (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      ((fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).restrictScalars ℝ := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
