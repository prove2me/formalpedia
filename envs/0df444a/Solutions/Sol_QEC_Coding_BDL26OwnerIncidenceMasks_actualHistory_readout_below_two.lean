-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.actualHistory_readout_below_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:15:10.474902+00:00
-- url     : https://prove2.me/submissions/fd138ac8-ea6a-4457-b5dd-ca9a5af1745b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_syndromeReadout_below_two


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (i : LevelIndex (n + 2)) (hi : i.val < 2) :
    LevelTwoHistory.syndromeReadout (indexedDecoderData S (n + 2))
      (actualHistory S n sigma) i = 0 :=
  LevelTwoHistory.syndromeReadout_below_two _ _ i hi
end QEC.Coding.BDL26OwnerIncidenceMasks
