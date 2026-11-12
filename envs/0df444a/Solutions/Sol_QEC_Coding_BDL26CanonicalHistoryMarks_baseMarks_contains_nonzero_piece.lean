-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.baseMarks_contains_nonzero_piece
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:41:53.936298+00:00
-- url     : https://prove2.me/submissions/afb122fa-e10f-4c3a-a119-0707f79b2759

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_baseMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (v : GraphVertex S 2)
    (h : basePiece S n sigma v ≠ 0) : v ∈ baseMarks S n sigma :=
  (mem_baseMarks S n sigma v).mpr (Or.inr (Or.inl h))
end QEC.Coding.BDL26CanonicalHistoryMarks
