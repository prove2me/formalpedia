-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.complexHessian_add_of_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:39.968806+00:00
-- url     : https://prove2.me/submissions/314f8e20-abfa-442a-85df-d9c5f94a838a

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_hessC_eq_lv

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
theorem _root_.solution (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  have hev : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w := by
    filter_upwards [hφ.eventually (by simp), hψ.eventually (by simp)] with w hw1 hw2
    exact fderiv_add (hw1.differentiableAt (by norm_num)) (hw2.differentiableAt (by norm_num))
  have hφ' : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hψ' : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD : fderiv ℝ (fderiv ℝ fun w => φ w + ψ w) z =
      fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z := by
    rw [hev.fderiv_eq]; exact fderiv_add hφ' hψ'
  ext i j
  simp only [hessC_eq_lv, lv, hD, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring
end ReciprocityTheory.AnForm.A.TraceConjugationCover
