-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.lap_eq_rot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:40.390971+00:00
-- url     : https://prove2.me/submissions/bcf801f9-c718-4d8b-8d05-91d5bdbbb90d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_ee_smul
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_iee_smul
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_laplacian_eq_fderiv_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A.GreenFunction
theorem _root_.solution (u : ℂ → ℝ) (z : ℂ) (θ : ℝ) :
    Δ u z = fderiv ℝ (fderiv ℝ u) z (ee θ) (ee θ)
      + fderiv ℝ (fderiv ℝ u) z (Complex.I * ee θ) (Complex.I * ee θ) := by
  rw [laplacian_eq_fderiv_fderiv, iee_smul, ee_smul]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  have hsc := Real.sin_sq_add_cos_sq θ
  set H := fderiv ℝ (fderiv ℝ u) z
  linear_combination (-(H 1 1 + H Complex.I Complex.I)) * hsc
end ReciprocityTheory.AnForm.A.GreenFunction
