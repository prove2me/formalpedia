-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.continuous_lap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:23.984812+00:00
-- url     : https://prove2.me/submissions/d5c90c76-fd3d-4c48-9094-7a760420301e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_laplacian_eq_fderiv_fderiv
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_continuous_fderiv_fderiv

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
theorem _root_.solution {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) : Continuous (Δ u) := by
  have h : Δ u = fun z =>
      fderiv ℝ (fderiv ℝ u) z 1 1 + fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I :=
    funext (laplacian_eq_fderiv_fderiv u)
  have hD2 := continuous_fderiv_fderiv hu
  rw [h]; fun_prop
end ReciprocityTheory.AnForm.A.GreenFunction
