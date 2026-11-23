-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_hessC_add__d2d06fbdee79
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:44.853533+00:00
-- url     : https://prove2.me/submissions/5ab070ed-9105-4d5a-a994-8663510ec390

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Complex Filter Topology
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  have hφ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ φ w :=
    (hφ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hψ' : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ ψ w :=
    (hψ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hE : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w :=
    (hφ'.and hψ').mono fun w hw => fderiv_add hw.1 hw.2
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdψ : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) z =
      fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z := by
    rw [hE.fderiv_eq]
    exact fderiv_add hdφ hdψ
  ext i j
  simp only [hessC, h2, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring
end ReciprocityTheory.AnForm.A
