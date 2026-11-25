-- Prove2me | solution 1 for PositivityTheory.KReal.getD_pad_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:39.510815+00:00
-- url     : https://prove2.me/submissions/7fbb5c2b-6552-448e-91c9-97d88ce07f81

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution (p k i : ℕ) (z : ℤ) :
    (pad (List.replicate p z) k []).getD i 0 = if i < p then (z : ℚ) else 0 := by
  simp only [pad, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  split_ifs <;> simp_all <;> omega
end PositivityTheory.KReal
