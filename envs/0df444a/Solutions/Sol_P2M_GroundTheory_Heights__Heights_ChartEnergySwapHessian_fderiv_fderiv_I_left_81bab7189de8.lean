-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_left_81bab7189de8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:30.002982+00:00
-- url     : https://prove2.me/submissions/3d46ca5b-6aca-4a44-8144-c20565b93934

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_right_e4d655698f84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_symm_af2925260adc

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
theorem _root_.solution {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y (Complex.I • u) v = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  rw [fderiv_fderiv_symm (hF.restrict_scalars ℝ), fderiv_fderiv_I_right hF,
    fderiv_fderiv_symm (hF.restrict_scalars ℝ)]
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
