-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.hess_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:31.968384+00:00
-- url     : https://prove2.me/submissions/cff7c560-3aae-4338-8266-e46726138015

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
variable {D E : ℕ}
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) (w b : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b =
      fderiv ℝ (fderiv ℝ φ) (τ z) (fderiv ℂ τ z w) (fderiv ℂ τ z b) +
      fderiv ℝ φ (τ z) (fderiv ℂ (fun x => fderiv ℂ τ x b) z w) := by
  have hτev : ∀ᶠ x in 𝓝 z, AnalyticAt ℂ τ x := hτ.eventually_analyticAt
  have hφev : ∀ᶠ y in 𝓝 (τ z), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hφev' : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ φ (τ x) :=
    hτ.continuousAt.tendsto.eventually hφev
  have heq : (fun x => fderiv ℝ (φ ∘ τ) x b) =ᶠ[𝓝 z]
      (fun x => fderiv ℝ φ (τ x) (fderiv ℂ τ x b)) := by
    filter_upwards [hτev, hφev'] with x hx hφx
    have hxR : DifferentiableAt ℝ τ x := hx.differentiableAt.restrictScalars ℝ
    rw [fderiv_comp x hφx hxR, hx.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  have hf2 : ContDiffAt ℝ 2 (φ ∘ τ) z :=
    hφ.comp z ((hτ.contDiffAt (n := 2)).restrict_scalars ℝ)
  have hD : DifferentiableAt ℝ (fderiv ℝ (φ ∘ τ)) z :=
    (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b = fderiv ℝ (fun x => fderiv ℝ (φ ∘ τ) x b) z w := by
    rw [fderiv_clm_apply hD (differentiableAt_const b)]
    simp
  rw [h1, heq.fderiv_eq]
  have hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) (τ z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hτR : DifferentiableAt ℝ τ z := hτ.differentiableAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun x => fderiv ℝ φ (τ x))
      ((fderiv ℝ (fderiv ℝ φ) (τ z)).comp (fderiv ℝ τ z)) z :=
    hφ2.hasFDerivAt.comp z hτR.hasFDerivAt
  have hg : DifferentiableAt ℂ (fun x => fderiv ℂ τ x b) z :=
    hτ.fderiv.differentiableAt.clm_apply (differentiableAt_const b)
  have hu : HasFDerivAt (fun x => fderiv ℂ τ x b)
      ((fderiv ℂ (fun x => fderiv ℂ τ x b) z).restrictScalars ℝ) z :=
    hg.hasFDerivAt.restrictScalars ℝ
  rw [(hc.clm_apply hu).fderiv]
  have hwR : fderiv ℝ τ z w = fderiv ℂ τ z w := by
    rw [hτ.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  simp [hwR, add_comm]
end ReciprocityTheory.AnForm.A.TraceConjugationCover
