-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fderiv_fderiv_re_analytic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:12.97899+00:00
-- url     : https://prove2.me/submissions/427faeb7-6a0e-4df0-87fd-4fc3956d137d

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.A
open Complex Filter Topology
noncomputable section
variable {D : ℕ}
private lemma fderiv_re_apply_lemma (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hg : DifferentiableAt ℂ g z) (v : Fin D → ℂ) :
    fderiv ℝ (fun w => (g w).re) z v = (fderiv ℂ g z v).re := by
  have h : HasFDerivAt (fun w => (g w).re)
      (Complex.reCLM.comp ((fderiv ℂ g z).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hg.hasFDerivAt.restrictScalars ℝ)
  rw [h.fderiv]
  rfl
end
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Complex Filter Topology
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z)
    (v u : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fun w => (G w).re)) z v u = (fderiv ℂ (fderiv ℂ G) z v u).re := by
  have hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)
  have hdΦ : DifferentiableAt ℝ (fderiv ℝ (fun w => (G w).re)) z :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ G w := hG.eventually_analyticAt
  have hE : (fun w => fderiv ℝ (fun w => (G w).re) w u) =ᶠ[𝓝 z]
      fun w => (fderiv ℂ G w u).re :=
    hA.mono fun w hw => fderiv_re_apply_lemma G w hw.differentiableAt u
  have hdG : DifferentiableAt ℂ (fun w => fderiv ℂ G w u) z :=
    (hG.fderiv.differentiableAt).clm_apply (differentiableAt_const u)
  have h1 : fderiv ℝ (fderiv ℝ (fun w => (G w).re)) z v u =
      fderiv ℝ (fun w => fderiv ℝ (fun w => (G w).re) w u) z v := by
    rw [fderiv_clm_apply hdΦ (differentiableAt_const u)]
    simp
  have h2 : fderiv ℂ (fun w => fderiv ℂ G w u) z v = fderiv ℂ (fderiv ℂ G) z v u := by
    rw [fderiv_clm_apply (hG.fderiv.differentiableAt) (differentiableAt_const u)]
    simp
  rw [h1, hE.fderiv_eq, fderiv_re_apply_lemma _ z hdG v, h2]
end ReciprocityTheory.AnForm.A
