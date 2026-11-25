-- Prove2me | solution 1 for ReciprocityTheory.AnForm.levi_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:37.74782+00:00
-- url     : https://prove2.me/submissions/585f4e64-06f7-4926-9504-31aad967248d

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Theorems.Thm_ReciprocityTheory_AnForm_sndDeriv_I_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace ReciprocityTheory.AnForm
theorem _root_.solution {φ : (κ → ℂ) → ℝ} {τ : (ι → ℂ) → (κ → ℂ)} {z : ι → ℂ} (w : ι → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    levi (φ ∘ τ) z w = levi φ (τ z) (fderiv ℂ τ z w) := by
  have hτR : ∀ n : ℕ∞, ContDiffAt ℝ n τ z := fun n => (hτ.contDiffAt (n := n)).restrict_scalars ℝ
  have hφ1 : ∀ᶠ x in 𝓝 (τ z), DifferentiableAt ℝ φ x :=
    (hφ.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hφ1' : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ φ (τ y) := hτ.continuousAt.eventually hφ1

  have hev : fderiv ℝ (φ ∘ τ) =ᶠ[𝓝 z] fun y => (fderiv ℝ φ (τ y)).comp (fderiv ℝ τ y) := by
    filter_upwards [hτ.eventually_analyticAt, hφ1'] with y hy hφy
    exact fderiv_comp y hφy (hy.differentiableAt.restrictScalars ℝ)
  have hdA : DifferentiableAt ℝ (fderiv ℝ φ) (τ z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdB : DifferentiableAt ℝ (fderiv ℝ τ) z :=
    ((hτR 2).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hτz : HasFDerivAt τ (fderiv ℝ τ z) z := ((hτR 1).differentiableAt one_ne_zero).hasFDerivAt
  have hc : HasFDerivAt (fun y => fderiv ℝ φ (τ y))
      ((fderiv ℝ (fderiv ℝ φ) (τ z)).comp (fderiv ℝ τ z)) z :=
    hdA.hasFDerivAt.comp z hτz

  have hD := hc.clm_comp hdB.hasFDerivAt
  have hB : fderiv ℝ τ z = (fderiv ℂ τ z).restrictScalars ℝ :=
    (hτ.differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv
  have hI := sndDeriv_I_I hτ w
  unfold levi
  rw [hev.fderiv_eq, hD.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, hI, map_neg, hB,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  ring
end ReciprocityTheory.AnForm
