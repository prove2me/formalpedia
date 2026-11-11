-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.actualBaseDecode_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:12:24.83286+00:00
-- url     : https://prove2.me/submissions/29a202ee-7bd3-4d8a-b633-d74bc0767ec4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_decode_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (S : OddScale) (n : Nat) : actualBaseDecode S n 0 = 0 :=
  BDL26LevelTwoDecoder.decode_zero S
end QEC.Coding.BDL26OwnerIncidenceMasks
