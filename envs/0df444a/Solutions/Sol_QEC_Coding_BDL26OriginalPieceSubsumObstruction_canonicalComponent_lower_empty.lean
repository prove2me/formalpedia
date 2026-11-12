-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonicalComponent_lower_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:31:53.863603+00:00
-- url     : https://prove2.me/submissions/380e0741-683c-42e9-8070-bee30094e76d

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
import Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_canonicalComponent_eq_component
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_component_lower_empty


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    lowerRegion S j (canonicalComponent S j p hp) = ∅ := by
  rw [canonicalComponent_eq_component]
  exact component_lower_empty S j _ p hp
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
