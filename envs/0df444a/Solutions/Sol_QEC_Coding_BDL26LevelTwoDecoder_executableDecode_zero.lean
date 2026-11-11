-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDecoder.executableDecode_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:46:15.431504+00:00
-- url     : https://prove2.me/submissions/238defd2-f622-46e4-8ccf-df61673d3cb0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_allWords_zero_first
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_lookup_zero_of_zero_first
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableLocal_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableSyndrome_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
namespace QEC.Coding.BDL26LevelTwoDecoder
theorem _root_.solution (S : OddScale) : executableDecode S 0 = 0 := by
  apply lookup_zero_of_zero_first
  · exact allWords_zero_first _
  · exact executableLocal_zero S
  · exact executableSyndrome_zero S
end QEC.Coding.BDL26LevelTwoDecoder
