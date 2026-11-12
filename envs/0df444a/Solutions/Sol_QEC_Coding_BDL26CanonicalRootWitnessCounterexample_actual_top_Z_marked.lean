-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_top_Z_marked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:47:49.280193+00:00
-- url     : https://prove2.me/submissions/79c47707-f9cb-4cad-8049-cb0ef6c80f2c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_top_owner_apply
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_top_output_input
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_physical
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalMarks_step
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_outputMarks_contains_syndrome
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_step


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
private theorem predicate_transport {N : Type} (P : N → Prop)
    {a b : N} (he : a = b) (hb : P b) : P a := by
  cases he
  exact hb
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
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (z : (state S 3).presentation.Z)
    (v : ZDoubleCylinderVertex (state S 3).presentation z S)
    (hp : sigma.val (⟨z,v⟩ : FamilyZ S 4 level4) ≠ 0) :
    actualTopNode S (zVertex S 3 z) ∈ BDL26CanonicalHistoryMarks.marks S 2 sigma := by
  have hi : (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (1 : StepIndex 2)).input.val
      (⟨z,v⟩ : FamilyZ S 4 level4) = sigma.val ⟨z,v⟩ :=
    congrArg (fun word : (CF S).Syndrome level4 => word.val ⟨z,v⟩)
      (actual_top_output_input S sigma)
  have habove : BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4) ∈
      BDL26CanonicalHistoryMarks.aboveMarks S 2 sigma (1 : StepIndex 2) := by
    unfold BDL26CanonicalHistoryMarks.aboveMarks
    exact @BDL26OwnerIncidenceMasks.outputMarks_contains_syndrome
      4 (FamilyX S 4) (FamilyQ S 4) (FamilyZ S 4)
      (fun j : LevelIndex 4 => (state S j.val).presentation.data.xFintype)
      (fun j : LevelIndex 4 => (state S j.val).presentation.data.qFintype)
      (fun j : LevelIndex 4 => (state S j.val).presentation.data.zFintype)
      (indexedDecoderData S 4) (LevelTwoHistory.physicalStep (1 : StepIndex 2))
      (GraphVertex S 4)
      (BDL26DecodingGraph.graphVertexFintype S 4)
      (BDL26DecodingGraph.graphVertexDecidableEq S 4)
      (BDL26CanonicalHistoryMarks.outputAt S 2 sigma (1 : StepIndex 2))
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2))
      (BDL26CanonicalHistoryMarks.pieceOwner S 2 sigma (1 : StepIndex 2)) (⟨z,v⟩ : FamilyZ S 4 level4) (fun hz => hp (hi.symm.trans hz))
  have hphysical : BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4) ∈
      BDL26CanonicalHistoryMarks.physicalMarks S 2 sigma (1 : StepIndex 2).succ :=
    predicate_transport
      (fun M : Finset (GraphVertex S 4) =>
        BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4) ∈ M)
      (BDL26CanonicalHistoryMarks.physicalMarks_step S 2 sigma (1 : StepIndex 2)) habove
  have hm : BDL26CanonicalHistoryMarks.physicalNode S 2 (1 : StepIndex 2).succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4)) ∈
        BDL26CanonicalHistoryMarks.marks S 2 sigma :=
    (BDL26CanonicalHistoryMarks.mem_marks_physical S 2 sigma (1 : StepIndex 2).succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) (⟨z,v⟩ : FamilyZ S 4 level4))).mpr hphysical
  have he : BDL26CanonicalHistoryMarks.physicalNode S 2 (1 : StepIndex 2).succ
      (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2) ⟨z,v⟩) =
        actualTopNode S (zVertex S 3 z) :=
    (congrArg (fun w : GraphVertex S 4 =>
      BDL26CanonicalHistoryMarks.physicalNode S 2 (2 : LevelIndex 2) w)
        (top_owner_apply S z v)).trans (actualTopNode_physical S (zVertex S 3 z)).symm
  exact he ▸ hm
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
