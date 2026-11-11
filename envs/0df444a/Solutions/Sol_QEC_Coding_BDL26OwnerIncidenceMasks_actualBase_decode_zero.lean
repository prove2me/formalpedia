-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.actualBase_decode_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:17:21.747243+00:00
-- url     : https://prove2.me/submissions/2737f5d6-ee5c-4e26-9640-3933735667b5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualBaseDecode_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (S : OddScale) (n : Nat) :
    (actualBase S n).decode 0 = 0 := actualBaseDecode_zero S n
end QEC.Coding.BDL26OwnerIncidenceMasks
