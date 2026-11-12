-- Prove2me | solution 1 for QEC.Coding.BDL26OriginalPieceSubsumObstruction.every_even_depth_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:33:14.732192+00:00
-- url     : https://prove2.me/submissions/1e53f224-8dbf-49c6-aba4-6bf7d5156350

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
import Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_canonical_component_subsum_obstruction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 2 ≤ k) :
    2*(k-2)+4 = 2*k ∧
    ∃ p : FamilyZ S (2*(k-2)+4) (TopIndex (2*(k-2)+4)),
    ∃ hp : (upperSyndrome S (k-2)).val p ≠ 0,
      ∀ A : Finset (Fin (topOutput S (k-2)).localComponents.length),
        maskWord (upperRegion S (k-2) (canonicalComponent S (k-2) p hp))
            (upperSyndrome S (k-2)).val +
          (indexedFamily S (2*(k-2)+4)).coboundary1 (TopIndex (2*(k-2)+4))
            (topPieceSubsum S (k-2) A) ≠
        ((indexedDecoderData S (2*(k-2)+4)).selectedMap ⟨2*(k-2)+3, by omega⟩).map2
          (maskWord (lowerRegion S (k-2) (canonicalComponent S (k-2) p hp))
            (topOutput S (k-2)).coarse.val) :=
  ⟨by omega, canonical_component_subsum_obstruction S (k-2)⟩
end QEC.Coding.BDL26OriginalPieceSubsumObstruction
