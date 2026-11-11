-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.actualHistory_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:01:18.190508+00:00
-- url     : https://prove2.me/submissions/5f9508ee-1e0b-4672-8aa3-b2f33b719045

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_syndrome


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    (indexedFamily S (n + 2)).coboundary1 (TopIndex (n + 2))
      (historyLiftedCorrection (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2)))
        (actualHistory S n sigma)) = sigma.val :=
  LevelTwoHistory.stoppedHistory_syndrome (n := n) (indexedDecoderData S (n + 2))
    (actualAboveTwoSteps S n) (actualBase S n) sigma
end QEC.Coding.BDL26OwnerIncidenceMasks
