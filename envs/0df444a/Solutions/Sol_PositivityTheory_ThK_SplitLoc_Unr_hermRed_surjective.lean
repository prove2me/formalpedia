-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.hermRed_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:38.420358+00:00
-- url     : https://prove2.me/submissions/543e73c0-aab9-4636-be63-d7b2292885fd

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
open GlobalTheory.SatakeBound
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (p : R) (a : Fin n → ℕ) (M : ℕ) :
    Function.Surjective (hermRed p a M) := fun d => by
  choose c hc using fun i j => Ideal.Quotient.factor_surjective (span_pow_le_min p (a i) M) (d i j)
  exact ⟨c, funext fun i => funext fun j => hc i j⟩
end PositivityTheory.ThK.SplitLoc.Unr
