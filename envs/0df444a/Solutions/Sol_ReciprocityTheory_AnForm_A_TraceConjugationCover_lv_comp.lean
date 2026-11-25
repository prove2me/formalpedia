-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:53.73739+00:00
-- url     : https://prove2.me/submissions/918d59b8-48f5-4ecf-b358-e8df2de26404

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_hess_comp

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
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) (a b : Fin D → ℂ) :
    lv (fderiv ℝ (fderiv ℝ (φ ∘ τ)) z) a b =
      lv (fderiv ℝ (fderiv ℝ φ) (τ z)) (fderiv ℂ τ z a) (fderiv ℂ τ z b) := by
  have hg : ∀ c : Fin D → ℂ, DifferentiableAt ℂ (fun x => fderiv ℂ τ x c) z := fun c =>
    hτ.fderiv.differentiableAt.clm_apply (differentiableAt_const c)
  have hGI : fderiv ℂ (fun x => fderiv ℂ τ x (I • b)) z =
      I • fderiv ℂ (fun x => fderiv ℂ τ x b) z := by
    have : (fun x => fderiv ℂ τ x (I • b)) = fun x => I • fderiv ℂ τ x b := by
      funext x; rw [map_smul]
    rw [this]
    exact ((hg b).hasFDerivAt.const_smul I).fderiv
  unfold lv
  rw [hess_comp φ τ z hτ hφ a b, hess_comp φ τ z hτ hφ (I • a) (I • b),
    hess_comp φ τ z hτ hφ a (I • b), hess_comp φ τ z hτ hφ (I • a) b, hGI]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul, I_mul_I, neg_one_smul, map_neg]
  push_cast
  ring
end ReciprocityTheory.AnForm.A.TraceConjugationCover
