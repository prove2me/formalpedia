-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.basePieceBoundary_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:41:26.095199+00:00
-- url     : https://prove2.me/submissions/4dbde752-b5ad-420c-b8eb-e38cef6fb396

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_basePiece_partition

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution :
    (∑ v : GraphVertex S 2, basePieceBoundary S n sigma v) =
      (baseInput S n sigma).val := by
  unfold basePieceBoundary
  rw [← map_sum, basePiece_partition]
  exact actualBaseDecode_rightInverse S n _
end QEC.Coding.BDL26CanonicalHistoryMarks
