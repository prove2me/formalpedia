-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.actualHistory_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:15:07.027269+00:00
-- url     : https://prove2.me/submissions/a1b573fa-13ef-47ce-ac22-d55ba6ce479a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_length


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    (actualHistory S n sigma).length = n + 1 :=
  LevelTwoHistory.stoppedHistory_length (n := n) (indexedDecoderData S (n + 2))
    (actualAboveTwoSteps S n) (actualBase S n) sigma
end QEC.Coding.BDL26OwnerIncidenceMasks
