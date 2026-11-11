-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:14:15.270295+00:00
-- url     : https://prove2.me/submissions/7759050a-4651-4cf9-bfb7-a42b17393c70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution : physicalMarks S n sigma (0 : LevelIndex n) =
    baseMarks S n sigma := rfl
end QEC.Coding.BDL26CanonicalHistoryMarks
