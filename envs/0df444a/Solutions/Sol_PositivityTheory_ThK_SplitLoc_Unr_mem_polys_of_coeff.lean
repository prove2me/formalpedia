-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.mem_polys_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:43.225133+00:00
-- url     : https://prove2.me/submissions/5605282a-a546-4e29-9b39-3c579234c784

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
open PowerSeries
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {f : PowerSeries ℂ} (N : ℕ) (h : ∀ t, N ≤ t → coeff t f = 0) : f ∈ polys := by
  refine ⟨trunc N f, ?_⟩
  ext t
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, coeff_trunc]
  split_ifs with ht
  · rfl
  · exact (h t (not_lt.mp ht)).symm
end PositivityTheory.ThK.SplitLoc.Unr
