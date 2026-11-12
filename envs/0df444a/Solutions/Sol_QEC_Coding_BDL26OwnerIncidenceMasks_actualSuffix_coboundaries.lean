-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.actualSuffix_coboundaries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:16:36.783279+00:00
-- url     : https://prove2.me/submissions/9e0f63cc-6be7-4596-aa19-2e5dd81f390a

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
    ((LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)).step i sigma).componentCoboundaries =
      (actualStep S (n + 2) (LevelTwoHistory.physicalStep i) sigma).componentCoboundaries := rfl
end QEC.Coding.BDL26OwnerIncidenceMasks
