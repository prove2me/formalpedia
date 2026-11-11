-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.basePiece_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:36:16.025646+00:00
-- url     : https://prove2.me/submissions/b946b8fc-d53c-4104-ac46-5b082f6f7649

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_sum_fiberPart


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution : (∑ v : GraphVertex S 2, basePiece S n sigma v) =
    baseCorrection S n sigma := sum_fiberPart _ _
end QEC.Coding.BDL26CanonicalHistoryMarks
