-- Prove2me | solution 1 for PositivityTheory.KReal.rat_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:47.856427+00:00
-- url     : https://prove2.me/submissions/edcde36c-d365-45b8-8cc4-60fc210c6e4b

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreComb
import Theorems.Thm_PositivityTheory_KReal_nat_facts

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
    (D.R : ℚ) + D.p + D.q = D.a + D.a' ∧ (D.S : ℚ) = D.p + D.q ∧ (D.P : ℚ) + D.p = D.a ∧ (D.Q : ℚ) = D.p ∧
      (D.P' : ℚ) = D.q ∧ (D.Q' : ℚ) + D.q = D.a' ∧ 2 * (nD D : ℚ) + D.a + D.a' = D.κ + 2 * D.p + 2 * D.q ∧
      2 * (mD D : ℚ) + 2 * D.p + 2 * D.q = D.κ + D.a + D.a' ∧ (D.a : ℚ) + D.a' < D.κ ∧
      2 * ((D.p : ℚ) + D.q) < D.a' ∧ (D.a' : ℚ) < D.a ∧ (0 : ℚ) ≤ D.p ∧ (0 : ℚ) ≤ D.q := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := nat_facts h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by positivity, by positivity⟩
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3
  · exact_mod_cast e4
  · exact_mod_cast e5
  · exact_mod_cast e6
  · exact_mod_cast e7
  · exact_mod_cast e8
  · exact_mod_cast h.h2
  · exact_mod_cast h.h5
  · exact_mod_cast h.a_gt
end PositivityTheory.KReal
