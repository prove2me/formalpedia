-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.topPieceSubsum_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:30:58.609814+00:00
-- url     : https://prove2.me/submissions/3c114061-33f7-4f44-9eca-6b24a2823807

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
import Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_outputPieceSubsum_univ

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    topPieceSubsum S j Finset.univ = (topOutput S j).correction :=
  outputPieceSubsum_univ S _ _ _
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
