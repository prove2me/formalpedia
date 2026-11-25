-- Prove2me | solution 1 for PositivityTheory.KReal.nm_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:13.222263+00:00
-- url     : https://prove2.me/submissions/9a8f7c94-ad56-4eac-a06b-232adc052e11

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreComb
import Theorems.Thm_PositivityTheory_KReal_nat_facts
import Theorems.Thm_PositivityTheory_KReal_rat_facts

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
theorem _root_.solution {D : RealData} (h : D.Hyp) :
    0 < nD D ∧ 0 < mD D ∧ ((D.κ : ℚ) / 2 = nD D + cPair D.R D.S) ∧ ((D.κ : ℚ) / 2 = mD D - cPair D.R D.S) ∧
      D.P ≤ D.R ∧ D.Q ≤ D.S ∧ D.Q' ≤ D.R ∧ D.P' ≤ D.S := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := nat_facts h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := rat_facts h
  have := h.h2; have := h.h5; have := h.a_gt
  refine ⟨by omega, by omega, ?_, ?_, by omega, by omega, by omega, by omega⟩
  · simp only [cPair]; linarith
  · simp only [cPair]; linarith
end PositivityTheory.KReal
