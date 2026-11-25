-- Prove2me | solution 1 for PositivityTheory.KReal.cw_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:05.77179+00:00
-- url     : https://prove2.me/submissions/a1c35767-983a-4dfa-ab48-d11beb2b0be5

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW

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
theorem _root_.solution {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    ν a = La a - 1 ∧ ν b = La b + 1 ∧ ∀ x, x ≠ a → x ≠ b → ν x = La x := by
  refine ⟨?_, ?_, ?_⟩
  · have := h a
    rw [if_pos rfl, if_neg hab] at this
    linarith
  · have := h b
    rw [if_neg (Ne.symm hab), if_pos rfl] at this
    linarith
  · intro x hxa hxb
    have := h x
    rw [if_neg hxa, if_neg hxb] at this
    linarith
end PositivityTheory.KReal
