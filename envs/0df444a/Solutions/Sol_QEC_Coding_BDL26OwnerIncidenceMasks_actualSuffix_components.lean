-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.actualSuffix_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:15:23.015282+00:00
-- url     : https://prove2.me/submissions/758362d4-b34c-4fd1-813a-b214efd32ec0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (S : OddScale) (n : Nat) (i : StepIndex n)
    (sigma : (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))).family.Syndrome i.succ) :
    ((LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)).step i sigma).localComponents =
      (actualStep S (n + 2) (LevelTwoHistory.physicalStep i) sigma).localComponents := rfl
end QEC.Coding.BDL26OwnerIncidenceMasks
