-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_comp_holo_687153abf862
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:03:09.678222+00:00
-- url     : https://prove2.me/submissions/622e4ad1-e409-4cf7-ad24-9badb867c141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_right_e4d655698f84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_I_left_81bab7189de8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_comp_ddc6e6556568
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_add_8ab3e1d1ce6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_cxHessian_of_form_cb255067719c

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
theorem _root_.solution (f g : (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ)) (h : (Fin D → ℂ) → ℂ)
    (y : Fin D → ℂ) (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℂ 2 F y) (hh : ContDiffAt ℂ 2 h y)
    (hf : f =ᶠ[𝓝 y] fun y' => g (F y') + (h y').re) :
    cxHessian f y = (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ *
      cxHessian g (F y) * (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map
        (starRingEnd ℂ) := by
  have hFR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hhR : ContDiffAt ℝ 2 h y := hh.restrict_scalars ℝ
  have hHess : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ fun y' => g (F y') + (h y').re) y := by
    have : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun y' => g (F y') + (h y').re) :=
      hf.eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq
    exact this.fderiv_eq
  have hre2 : ContDiffAt ℝ 2 (fun y' => (h y').re) y := Complex.reCLM.contDiff.contDiffAt.comp y hhR
  have hsum := fderiv_fderiv_add (f₁ := fun y' => g (F y')) (f₂ := fun y' => (h y').re) (hg.comp y hFR) hre2
  have hre : ∀ u v, fderiv ℝ (fderiv ℝ fun y' => (h y').re) y u v =
      Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v) := by
    intro u v
    have := fderiv_fderiv_comp (g := ⇑Complex.reCLM) (F := h) Complex.reCLM.contDiff.contDiffAt hhR u v
    have h0 : fderiv ℝ (fderiv ℝ (⇑Complex.reCLM)) (h y) = 0 := by
      have : fderiv ℝ (⇑Complex.reCLM) = fun _ => Complex.reCLM := funext fun _ => Complex.reCLM.fderiv
      rw [this]
      exact fderiv_const_apply _
    rw [h0, Complex.reCLM.fderiv] at this
    simpa using this
  have hLF : ∀ u, fderiv ℝ F y u = fderiv ℂ F y u := fun u => by
    rw [(hF.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
    rfl
  refine cxHessian_of_form f g y (F y) (fderiv ℂ F y)
    (fun u v => fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) + Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v))
    ?_ ?_ ?_
  · intro u v
    rw [hHess, hsum, _root_.add_apply, _root_.add_apply, fderiv_fderiv_comp hg hFR,
      hre, hLF, hLF]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh]
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
