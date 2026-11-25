-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_right_e4d655698f84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:10.560519+00:00
-- url     : https://prove2.me/submissions/a7ef6273-2213-486e-b340-b9f5931bda4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_eventually_fderiv_I_smul_cb450053cee6

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
    fderiv ℝ (fderiv ℝ F) y u (Complex.I • v) = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  have hR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun y' => fderiv ℝ F y' (Complex.I • v))
      ((fderiv ℝ (fderiv ℝ F) y).flip (Complex.I • v)) y := by
    simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • v) y)
  have h2 : HasFDerivAt (fun y' => Complex.I • fderiv ℝ F y' v)
      (Complex.I • (fderiv ℝ (fderiv ℝ F) y).flip v) y := by
    have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).const_smul Complex.I
    simpa [Pi.smul_def] using this
  have h3 := h2.congr_of_eventuallyEq ((eventually_fderiv_I_smul hF).mono fun y' hy' => hy' v)
  have := congrArg (fun L => L u) (h1.unique h3)
  simpa using this
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
