-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonicalComponent_eq_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:21:04.944447+00:00
-- url     : https://prove2.me/submissions/d633d5c3-eed2-4d80-a6d0-fc10d202746a

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
import Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_canonicalComponent_singleton
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_component_singleton


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    canonicalComponent S j p hp = component S j (canonicalLowerMarks S j) p hp := by
  rw [canonicalComponent_singleton, component_singleton]
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
