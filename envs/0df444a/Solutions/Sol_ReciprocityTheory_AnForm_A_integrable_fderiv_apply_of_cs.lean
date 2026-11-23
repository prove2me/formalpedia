-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integrable_fderiv_apply_of_cs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:11.071512+00:00
-- url     : https://prove2.me/submissions/1138db06-a915-4382-ab7a-82a516cff4ce

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc

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
    (hcs : HasCompactSupport g) (u : Fin D → ℂ) : Integrable (fun z => fderiv ℝ g z u) := by
  have hc : Continuous fun z => fderiv ℝ g z u :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine hc.integrable_of_hasCompactSupport ?_
  exact (hcs.fderiv ℝ).mono fun z hz h0 => hz (by simp [h0])
end ReciprocityTheory.AnForm.A
