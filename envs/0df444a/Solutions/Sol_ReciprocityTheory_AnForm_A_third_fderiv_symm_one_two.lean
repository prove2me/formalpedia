-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.third_fderiv_symm_one_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:39.840808+00:00
-- url     : https://prove2.me/submissions/3d58631e-5b85-4f29-8a15-a726d343d5ae

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
theorem _root_.solution {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (h : ContDiffAt ℝ 3 φ z)
    (u x : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u x = fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z x u := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ φ) z := h.fderiv_right (by first | norm_num | simp | rfl)
  exact h2.isSymmSndFDerivAt (by first | simp | norm_num | (simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)) u x
end ReciprocityTheory.AnForm.A
