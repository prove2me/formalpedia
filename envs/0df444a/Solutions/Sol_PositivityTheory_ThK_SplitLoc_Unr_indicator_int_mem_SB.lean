-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.indicator_int_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:16:52.482776+00:00
-- url     : https://prove2.me/submissions/9372104f-a2d6-43ab-8c5f-ed53357cefb5

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


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
theorem _root_.solution {A D : Type} [Fintype A] [Fintype D] :
    Set.indicator {X : Matrix A D k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix A D k → ℂ) ∈ SB _ := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  classical
  have hK := isCompact_intMatrix (k := k) (m := A) (n := D)
  have hcl : IsClopen {X : Matrix A D k | ∀ i j, X i j ∈ 𝒪[k]} := ⟨hK.isClosed, isOpen_intMatrix⟩
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const (Matrix A D k) (1 : ℂ)) hcl).isLocallyConstant
end PositivityTheory.ThK.SplitLoc.Unr
