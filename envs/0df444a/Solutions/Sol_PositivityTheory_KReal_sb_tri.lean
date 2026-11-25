-- Prove2me | solution 1 for PositivityTheory.KReal.sb_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:24.235731+00:00
-- url     : https://prove2.me/submissions/f1e326c5-bc12-4675-8b7e-a0b6d269c2e4

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
theorem _root_.solution {a b : Ix r s} (h : sameBlock a b) : a = b ∨ posC a b ∨ posC b a := by
  cases a <;> cases b <;> simp only [sameBlock, posC, Sum.inl.injEq, Sum.inr.injEq] at h ⊢
  · rename_i i j
    rcases lt_trichotomy i j with h | h | h <;> simp [h]
  · rename_i i j
    rcases lt_trichotomy i j with h | h | h <;> simp [h]
end PositivityTheory.KReal
