-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonical_component_subsum_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:26:12.017622+00:00
-- url     : https://prove2.me/submissions/07950f89-e6c7-4d31-89f6-84fa9c9aa86a

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
import Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_component_subsum_obstruction
import Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_canonicalComponent_eq_component

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    ∃ p : FamilyZ S (2*j+4) (TopIndex (2*j+4)),
    ∃ hp : (upperSyndrome S j).val p ≠ 0,
      ∀ A : Finset (Fin (topOutput S j).localComponents.length),
        maskWord (upperRegion S j (canonicalComponent S j p hp)) (upperSyndrome S j).val +
          (indexedFamily S (2*j+4)).coboundary1 (TopIndex (2*j+4))
            (topPieceSubsum S j A) ≠
        ((indexedDecoderData S (2*j+4)).selectedMap ⟨2*j+3, by omega⟩).map2
          (maskWord (lowerRegion S j (canonicalComponent S j p hp))
            (topOutput S j).coarse.val) := by
  obtain ⟨p,hp,h⟩ := component_subsum_obstruction S j (canonicalLowerMarks S j)
  refine ⟨p,hp,?_⟩
  intro A
  rw [canonicalComponent_eq_component]
  exact h A
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
