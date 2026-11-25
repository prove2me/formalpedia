-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_comp_ddc6e6556568
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:42.075954+00:00
-- url     : https://prove2.me/submissions/5bd3487c-72e0-4971-bd9e-6958def6aa07

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
theorem _root_.solution {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : G → ℝ}
    {F : (Fin D → ℂ) → G} {y : Fin D → ℂ} (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ fun y' => g (F y')) y u v =
      fderiv ℝ (fderiv ℝ g) (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) +
        fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) := by
  have hgev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ g (F y') :=
    hF.continuousAt.tendsto.eventually
      ((hg.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
  have hFev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ F y' :=
    (hF.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => g (F y')) =ᶠ[𝓝 y]
      fun y' => (fderiv ℝ g (F y')).comp (fderiv ℝ F y') := by
    filter_upwards [hgev, hFev] with y' h1 h2
    exact fderiv_comp y' h1 h2
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) (F y) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y' => fderiv ℝ g (F y'))
      ((fderiv ℝ (fderiv ℝ g) (F y)).comp (fderiv ℝ F y)) y :=
    hgd.hasFDerivAt.comp y (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hall := (hc.clm_comp hFd.hasFDerivAt).congr_of_eventuallyEq heq
  rw [hall.fderiv]
  simp [add_comm]
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
