-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.outputPieceSubsum_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:05:03.244275+00:00
-- url     : https://prove2.me/submissions/a4d87524-3acf-4416-8e7a-f87fcc149f1e

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (O : AssemblyStepOutput (indexedDecoderData S depth) i) :
    outputPieceSubsum S depth i O Finset.univ = O.correction := by
  change (∑ a : Fin O.localComponents.length, O.localComponents.get a) = O.correction
  rw [← Fin.sum_ofFn, List.ofFn_get]
  exact O.correction_decomposition.symm
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
