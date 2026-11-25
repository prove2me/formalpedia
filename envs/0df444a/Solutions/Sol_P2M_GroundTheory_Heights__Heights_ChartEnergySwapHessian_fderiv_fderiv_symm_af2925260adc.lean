-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_symm_af2925260adc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:43.646369+00:00
-- url     : https://prove2.me/submissions/c3bae236-30c0-4e21-a3f1-421e9f950798

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
omit [NormedSpace ℂ E'] [IsScalarTower ℝ ℂ E']
namespace GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
theorem _root_.solution {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) : fderiv ℝ (fderiv ℝ F) y u v = fderiv ℝ (fderiv ℝ F) y v u :=
  hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) u v
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
