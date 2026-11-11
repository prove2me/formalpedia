-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDecoder.executableLocal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:53:57.917264+00:00
-- url     : https://prove2.me/submissions/154c0495-ee50-45dc-804f-254c19b1715e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_rawLocal_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
namespace QEC.Coding.BDL26LevelTwoDecoder
theorem _root_.solution (S : OddScale) : executableLocal S 0 = true :=
  rawLocal_zero _ S (executableOwnerAtZero S)
end QEC.Coding.BDL26LevelTwoDecoder
