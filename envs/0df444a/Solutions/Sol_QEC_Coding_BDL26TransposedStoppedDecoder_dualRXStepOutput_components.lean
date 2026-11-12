-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualRXStepOutput_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:42:56.65321+00:00
-- url     : https://prove2.me/submissions/46a61550-9700-4c1e-8a1e-dc4e6f87954e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26RXDecoderAdapter
open MultiscaleDecoder Coordinates
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ) :
    (dualRXStepOutput S depth i h sigma).localComponents =
      (BDL26RZDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S (dualRXMaterializedInput S depth i h sigma)).localComponents.map
        (wordEquiv (dualRXTopQ S depth i h)) := rfl
end QEC.Coding.BDL26TransposedStoppedDecoder
