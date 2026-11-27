-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.unifBaseChangeInj_of_seamsCS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:36:58.75068+00:00
-- url     : https://prove2.me/submissions/824c7096-e37c-42de-97cd-516d60b0f1d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_IsPullUnifPre_toIsPullUnif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out
theorem _root_.solution (h1 : PullDegCSInjSt) (h2 : PullPreCSInjSt)
    (h3 : ExpPullInjSt) : UnifBaseChangeInjSt := by
  intro R R' _ _ _ _ I I' hR hR' φ hI hφ D A G _ _ hG U W hW hgen G' _ _ bc hbc A' hA' eA heA hwA
    L' wL he hwL hrig
  obtain ⟨D', hD, hCS⟩ := h1 R R' I I' hR hR' φ hI hφ D A G hG U W hW hgen G' bc hbc A' hA' eA heA
    hwA L' wL he hwL hrig
  obtain ⟨U', hL, hg, hP⟩ := h2 R R' I I' hR hR' φ hI hφ D A G hG U W hW hgen G' bc hbc A' hA' eA heA
    hwA L' wL he hwL hrig D' hD hCS
  have hx := h3 R R' I I' hR hR' φ hI hφ D A G hG U W hW hgen G' bc hbc A' hA' eA heA hwA
    L' wL he hwL hrig D' hD U' hL hg hP
  exact ⟨D', hD, { toUnifPre := U', expand := hx }, hL, hg, IsPullUnifPre.toIsPullUnif hP⟩
end ReciprocityTheory.ChartRestriction.G.Out
