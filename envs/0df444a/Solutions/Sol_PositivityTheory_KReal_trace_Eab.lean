-- Prove2me | solution 1 for PositivityTheory.KReal.trace_Eab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:24.933882+00:00
-- url     : https://prove2.me/submissions/34b6aa04-3634-4b08-921d-b7e97d1acc2d

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv

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
variable {p q : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (a b : Ix p q) : (Eab a b).trace = if a = b then 1 else 0 := by
  simp [Eab, Matrix.trace, Matrix.single_apply, Matrix.diag]
  split_ifs with h
  · subst h
    simp [Finset.filter_eq]
  · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2⟩
    exact h (h1.trans h2.symm)
end PositivityTheory.KReal
