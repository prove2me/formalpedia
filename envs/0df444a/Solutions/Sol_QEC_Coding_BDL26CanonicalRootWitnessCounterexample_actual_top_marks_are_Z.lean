-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_top_marks_are_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:38:37.741208+00:00
-- url     : https://prove2.me/submissions/fa1fb28f-3a21-4105-bde4-514973099eb5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_aboveMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_physical
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
private theorem actualTopNode_physical (S : OddScale) (v : GraphVertex S 4) :
    actualTopNode S v = BDL26CanonicalHistoryMarks.physicalNode S 2 (2 : LevelIndex 2) v := rfl
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
end

set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2) :
    ∀ v : GraphVertex S 4,
      actualTopNode S v ∈
        BDL26CanonicalHistoryMarks.marks S 2 sigma → ∃ z, v = zVertex S 3 z := by
  intro v hv
  have hv' : BDL26CanonicalHistoryMarks.physicalNode S 2 (2 : LevelIndex 2) v ∈
      BDL26CanonicalHistoryMarks.marks S 2 sigma :=
    Eq.mp (congrArg (fun w : BDL26CanonicalHistoryMarks.Node S 2 =>
      w ∈ BDL26CanonicalHistoryMarks.marks S 2 sigma) (actualTopNode_physical S v)) hv
  have hm := (BDL26CanonicalHistoryMarks.mem_marks_physical S 2 sigma
    (2 : LevelIndex 2) v).mp hv'
  change v ∈ BDL26CanonicalHistoryMarks.aboveMarks S 2 sigma (1 : StepIndex 2) at hm
  rcases (BDL26CanonicalHistoryMarks.mem_aboveMarks S 2 sigma (1 : StepIndex 2) v).mp hm with
    ⟨p,ho,_⟩ | ⟨a,ho,_⟩ | ⟨a,p,ho,_⟩
  · change zVertex S 3 p.1 = v at ho
    exact ⟨p.1,ho.symm⟩
  · change zVertex S 3 _ = v at ho
    exact ⟨_,ho.symm⟩
  · change zVertex S 3 p.1 = v at ho
    exact ⟨p.1,ho.symm⟩
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
