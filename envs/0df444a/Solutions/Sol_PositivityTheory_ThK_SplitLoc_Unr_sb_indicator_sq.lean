-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.sb_indicator_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:58.379351+00:00
-- url     : https://prove2.me/submissions/420338e1-acec-4959-944a-44aaae06cdf9

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int


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
  [MeasurableSpace k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution (n : ℕ) :
    Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin n) (Fin n) k → ℂ) ∈ SB _ := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have he : {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} =
      Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (𝒪[k] : Set k) := by
    ext X
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hc : IsCompact {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} := by
    rw [he]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => Model.isCompact_int
  have ho : IsOpen {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} := by
    rw [he]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => Model.isOpen_int
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hc.isClosed, ho⟩).isLocallyConstant
end PositivityTheory.ThK.SplitLoc.Unr
