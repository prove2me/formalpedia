-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.physicalNode_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:24:31.976975+00:00
-- url     : https://prove2.me/submissions/d605e67e-1bf0-4db7-a164-28e0d04228b7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) :
    (physicalNode S n i v).1.val = i.val + 2 := rfl
end QEC.Coding.BDL26CanonicalHistoryMarks
