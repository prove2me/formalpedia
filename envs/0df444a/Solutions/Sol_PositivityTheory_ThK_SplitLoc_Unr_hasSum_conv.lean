-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.hasSum_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:07.96013+00:00
-- url     : https://prove2.me/submissions/a4c712b5-1dbd-4ac7-b7e3-f6174a92d754

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
theorem _root_.solution {P : Polynomial ℂ} {n : ℕ} (hP : P.natDegree ≤ n) {f : ℤ → ℂ} {S : ℂ} (hf : HasSum f S) :
    HasSum (conv P n f) (P.eval 1 * S) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_mul]
  refine hasSum_sum fun j _ => ?_
  rw [one_pow, mul_one]
  exact ((Equiv.subRight (j : ℤ)).hasSum_iff.mpr hf).mul_left _
end PositivityTheory.ThK.SplitLoc.Unr
