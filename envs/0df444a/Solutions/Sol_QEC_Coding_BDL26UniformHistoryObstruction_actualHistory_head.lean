-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.actualHistory_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:20:47.383702+00:00
-- url     : https://prove2.me/submissions/e0e09250-896a-4aa7-9a9e-ffc218901b19

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_head


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    ∃ tail, actualHistory S (2 * j + 2) (upperSyndrome S j) =
      CorrectionHistoryEntry.step (Fin.last (2 * j + 1))
        (LevelTwoHistory.suffixOutput (indexedDecoderData S (2 * j + 4))
          (Fin.last (2 * j + 1)) (topOutput S j)) :: tail :=
  LevelTwoHistory.stoppedHistory_head (2 * j + 1) (indexedDecoderData S (2 * j + 4))
    (actualAboveTwoSteps S (2 * j + 2)) (actualBase S (2 * j + 2)) (upperSyndrome S j)
end QEC.Coding.BDL26UniformHistoryObstruction
