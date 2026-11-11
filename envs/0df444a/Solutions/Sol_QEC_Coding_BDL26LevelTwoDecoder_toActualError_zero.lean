-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDecoder.toActualError_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:15:46.073123+00:00
-- url     : https://prove2.me/submissions/3bd4ef5e-00c9-4a70-80b9-2f1dcdcdef83

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
namespace QEC.Coding.BDL26LevelTwoDecoder
theorem _root_.solution (S : OddScale) : toActualError S 0 = 0 := rfl
end QEC.Coding.BDL26LevelTwoDecoder
