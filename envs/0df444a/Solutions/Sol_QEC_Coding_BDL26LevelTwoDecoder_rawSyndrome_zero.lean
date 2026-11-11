-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDecoder.rawSyndrome_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:32:56.736608+00:00
-- url     : https://prove2.me/submissions/e38884ee-08f3-4e46-967c-4c346c2fea6d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_syndromeFromBits_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
namespace QEC.Coding.BDL26LevelTwoDecoder
theorem _root_.solution (P : TannerSquarePresentation)
    (hasA : Nonempty (TannerSquareAdmissible P)) (S : OddScale) :
    rawSyndrome P hasA S 0 = 0 := syndromeFromBits_zero _ _
end QEC.Coding.BDL26LevelTwoDecoder
