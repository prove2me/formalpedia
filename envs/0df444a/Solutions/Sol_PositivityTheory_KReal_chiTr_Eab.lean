-- Prove2me | solution 1 for PositivityTheory.KReal.chiTr_Eab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:24:51.924889+00:00
-- url     : https://prove2.me/submissions/3813f313-4d52-436d-b73d-834ed4b12a48

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSplit

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
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (c : ℂ) (a b : Ix p q) : chiTr c (Eab a b) = if a = b then c else 0 := by
  unfold chiTr Eab
  by_cases h : a = b
  · subst h
    simp
  · rw [Matrix.trace_single_eq_of_ne _ _ _ h]
    simp [h]
end PositivityTheory.KReal
