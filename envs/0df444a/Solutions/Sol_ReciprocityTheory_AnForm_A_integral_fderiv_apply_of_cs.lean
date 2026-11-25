-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_fderiv_apply_of_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:33.384323+00:00
-- url     : https://prove2.me/submissions/b8a3bb78-851b-46cb-ba73-951cdc2d1a6d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_fderiv_apply_of_cs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} {g : (Fin D → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) (u : Fin D → ℂ) : ∫ z, fderiv ℝ g z u = 0 := by
  have hd := hg.differentiable one_ne_zero
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Fin D → ℂ => (1 : ℂ)) (g := g) (v := u)
    (by simp) (by simpa using integrable_fderiv_apply_of_cs hg hcs u)
    (by simpa using (hg.continuous.integrable_of_hasCompactSupport hcs))
    (fun x _ => differentiableAt_const _) (fun x _ => hd x)
  simpa using h
end ReciprocityTheory.AnForm.A
