-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.differentiableAt_snd_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:30.89177+00:00
-- url     : https://prove2.me/submissions/298b6326-67b0-43ca-808f-ba99e2944520

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : ContDiffAt ℝ 3 φ z) : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ φ)) z := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ φ) z := h.fderiv_right (by first | norm_num | simp | rfl)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ φ)) z := h2.fderiv_right (by first | norm_num | simp | rfl)
  exact h1.differentiableAt (by first | norm_num | simp | exact one_ne_zero)
end ReciprocityTheory.AnForm.A
