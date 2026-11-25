-- Prove2me | solution 1 for PositivityTheory.KReal.pos_asymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:55.11252+00:00
-- url     : https://prove2.me/submissions/b73e8fff-4bb6-4c49-8c95-c232ade0cfa4

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc

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
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {a b : Ix r s} (h : posC a b) : ¬ posC b a := by
  cases a <;> cases b <;> simp only [posC] at h ⊢
  · exact not_lt.2 h.le
  · exact not_lt.2 h.le
end PositivityTheory.KReal
