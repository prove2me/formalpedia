-- Prove2me | solution 1 for PositivityTheory.KReal.pad_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:36.787655+00:00
-- url     : https://prove2.me/submissions/f168d476-606f-4d16-bc11-1e142e9169b6

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CorePair

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
theorem _root_.solution (k : ℕ) (z : ℤ) (i : Fin k) :
    (pad [] (k - ([] : List ℤ).length - (List.replicate k z).length) (List.replicate k z)).getD i 0 = (z : ℚ) := by
  simp [pad, List.getD_eq_getElem?_getD]
end PositivityTheory.KReal
