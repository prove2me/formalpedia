-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.indicator_int_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:04.657333+00:00
-- url     : https://prove2.me/submissions/88d62b69-fca1-4b5e-b542-615f82c8b75a

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_int_mul

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
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {A B C : Type} [Fintype B] [Fintype C] [DecidableEq B] {M : Matrix B C k} {R : Matrix C B k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hR : ∀ i j, R i j ∈ 𝒪[k]) (hMR : M * R = 1) (g : Matrix A B k) :
    Set.indicator {X : Matrix A C k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix A C k → ℂ) (g * M) =
      Set.indicator {X : Matrix A B k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix A B k → ℂ) g := by
  have key : (∀ i j, (g * M) i j ∈ 𝒪[k]) ↔ ∀ i j, g i j ∈ 𝒪[k] := by
    refine ⟨fun h => ?_, fun h => int_mul h hM⟩
    have := int_mul h hR
    rwa [Matrix.mul_assoc, hMR, Matrix.mul_one] at this
  by_cases hg : ∀ i j, g i j ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (show g * M ∈ {X : Matrix A C k | ∀ i j, X i j ∈ 𝒪[k]} from key.2 hg),
      Set.indicator_of_mem (show g ∈ {X : Matrix A B k | ∀ i j, X i j ∈ 𝒪[k]} from hg)]
    rfl
  · rw [Set.indicator_of_notMem (show g * M ∉ {X : Matrix A C k | ∀ i j, X i j ∈ 𝒪[k]} from fun h => hg (key.1 h)),
      Set.indicator_of_notMem (show g ∉ {X : Matrix A B k | ∀ i j, X i j ∈ 𝒪[k]} from hg)]
end PositivityTheory.ThK.SplitLoc.Unr
