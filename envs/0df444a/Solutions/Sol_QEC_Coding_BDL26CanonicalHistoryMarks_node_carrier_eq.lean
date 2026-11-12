-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.node_carrier_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:26:07.019056+00:00
-- url     : https://prove2.me/submissions/e53c2e86-e3b9-4b32-abaa-6028e7eaf7d2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution : Node S n = (decodingGraph S (n + 2)).Node := rfl
end QEC.Coding.BDL26CanonicalHistoryMarks
