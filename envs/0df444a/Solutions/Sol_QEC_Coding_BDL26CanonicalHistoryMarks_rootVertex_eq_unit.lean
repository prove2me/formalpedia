-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.rootVertex_eq_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:26:18.647362+00:00
-- url     : https://prove2.me/submissions/41a40762-1aa5-4cd2-9594-b02278249830

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution : rootVertex S = () := rfl
end QEC.Coding.BDL26CanonicalHistoryMarks
