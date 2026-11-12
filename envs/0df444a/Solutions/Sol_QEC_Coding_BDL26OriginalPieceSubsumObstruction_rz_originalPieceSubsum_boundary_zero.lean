-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.rz_originalPieceSubsum_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:30:06.812317+00:00
-- url     : https://prove2.me/submissions/565383ff-94ab-4f40-9c39-44b0802c52f5

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_map2_component_boundary_zero
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0)
    (s : (indexedFamily S depth).Syndrome i.castSucc)
    (A : Finset (Fin (BDL26RZDecoderAdapter.rzStepOutput S depth i h
      (BDL26RZDecoderAdapter.embeddedSyndrome S depth i s)).localComponents.length)) :
    (indexedFamily S depth).coboundary1 i.succ
      (outputPieceSubsum S depth i
        (BDL26RZDecoderAdapter.rzStepOutput S depth i h
          (BDL26RZDecoderAdapter.embeddedSyndrome S depth i s)) A) = 0 := by
  rw [outputPieceSubsum, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  have hb := AssemblyStepOutput.componentCoboundaryAt_eq
    (D := indexedDecoderData S depth) (i := i)
    (BDL26RZDecoderAdapter.rzStepOutput S depth i h
      (BDL26RZDecoderAdapter.embeddedSyndrome S depth i s)) a
  exact hb.symm.trans
    (BDL26RZDecoderAdapter.rzStepOutput_map2_component_boundary_zero S depth i h s a)
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
