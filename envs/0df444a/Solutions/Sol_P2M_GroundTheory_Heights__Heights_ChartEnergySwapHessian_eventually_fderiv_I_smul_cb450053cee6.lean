-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_eventually_fderiv_I_smul_cb450053cee6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:38.970312+00:00
-- url     : https://prove2.me/submissions/d1f135a4-86a1-4394-8e5d-e80e9799e32d

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
theorem _root_.solution {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y) :
    ∀ᶠ y' in 𝓝 y, ∀ v, fderiv ℝ F y' (Complex.I • v) = Complex.I • fderiv ℝ F y' v := by
  filter_upwards [hF.eventually (by simp)] with y' hy' v
  rw [(hy'.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
  simp
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
