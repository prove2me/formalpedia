-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.topPieceSubsum_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:14:06.018248+00:00
-- url     : https://prove2.me/submissions/9bfde38a-ad18-4f22-aa75-9436130e7b5f

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
import Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_topOutput_piece_boundary_zero
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (j : Nat)
    (A : Finset (Fin (topOutput S j).localComponents.length)) :
    (indexedFamily S (2*j+4)).coboundary1 (TopIndex (2*j+4))
      (topPieceSubsum S j A) = 0 := by
  rw [topPieceSubsum, outputPieceSubsum, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  have hb := AssemblyStepOutput.componentCoboundaryAt_eq
    (D := indexedDecoderData S (2*j+4)) (i := ⟨2*j+3, by omega⟩) (topOutput S j) a
  exact hb.symm.trans (topOutput_piece_boundary_zero S j a)
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
