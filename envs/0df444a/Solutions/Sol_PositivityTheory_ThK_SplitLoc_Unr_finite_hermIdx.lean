-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.finite_hermIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:47.877848+00:00
-- url     : https://prove2.me/submissions/1273f43f-13af-44a4-bd6d-273a82e6cf41

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SatakeTrivialRangeBound_one_lt_resCard
import Theorems.Thm_GlobalTheory_SatakeBound_card_hermIdx
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard


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
omit [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {p : 𝒪[k]} (hp : Irreducible p) {n : ℕ} (a : Fin n → ℕ) : Finite (HermIdx p a) := by
  have hq := GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  exact Nat.finite_of_card_ne_zero (by rw [card_hermIdx hp]; positivity)
end PositivityTheory.ThK.SplitLoc.Unr
