-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDecoder.baseAdapter_decode_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:12:55.975194+00:00
-- url     : https://prove2.me/submissions/9c437b3e-1a02-46dc-9990-c1c0d4c73e81

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_decode_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
namespace QEC.Coding.BDL26LevelTwoDecoder
theorem _root_.solution (S : OddScale) : (baseAdapter S).decode 0 = 0 :=
  decode_zero S
end QEC.Coding.BDL26LevelTwoDecoder
