-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementSupport.rxDelta1_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:00:32.036546+00:00
-- url     : https://prove2.me/submissions/a43987d6-2219-4488-90b5-d0e1e3511df2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxBoundary2Matrix_decomposition

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical
namespace QEC.Coding.BDL26ReplacementSupport
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) :
    wordLinearMapTranspose (rxBoundary2 P S) =
      rxLocalDelta1 P S + rxConnectingXQ1 P S + rxConnectingQZ1 P S := by
  classical
  unfold rxBoundary2 rxLocalDelta1 rxConnectingXQ1 rxConnectingQZ1
  rw [rxBoundary2Matrix_decomposition, map_add, map_add,
    wordLinearMapTranspose_add, wordLinearMapTranspose_add]
end QEC.Coding.BDL26ReplacementSupport
