-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonicalComponent_upper_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:32:49.403173+00:00
-- url     : https://prove2.me/submissions/662c52fd-3e77-49e2-bfed-7e2143103e88

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
import Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_canonicalComponent_eq_component
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_component_upper_self


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    p ∈ upperRegion S j (canonicalComponent S j p hp) := by
  rw [canonicalComponent_eq_component]
  exact component_upper_self S j _ p hp
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
