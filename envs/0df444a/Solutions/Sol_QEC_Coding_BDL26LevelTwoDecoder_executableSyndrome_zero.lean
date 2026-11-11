-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDecoder.executableSyndrome_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:38:50.799002+00:00
-- url     : https://prove2.me/submissions/5ad28e6f-2d40-45d7-adb6-161a52f0f243

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_rawSyndrome_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
namespace QEC.Coding.BDL26LevelTwoDecoder
theorem _root_.solution (S : OddScale) : executableSyndrome S 0 = 0 :=
  rawSyndrome_zero _ _ S
end QEC.Coding.BDL26LevelTwoDecoder
