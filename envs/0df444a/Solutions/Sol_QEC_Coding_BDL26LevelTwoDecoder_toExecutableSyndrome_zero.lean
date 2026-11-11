-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDecoder.toExecutableSyndrome_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:15:40.31972+00:00
-- url     : https://prove2.me/submissions/1e56adde-58f5-4059-b588-50d9e7128ba1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
namespace QEC.Coding.BDL26LevelTwoDecoder
theorem _root_.solution (S : OddScale) : toExecutableSyndrome S 0 = 0 := rfl
end QEC.Coding.BDL26LevelTwoDecoder
