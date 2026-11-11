-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualStepOutput_zero_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:13:18.524991+00:00
-- url     : https://prove2.me/submissions/befe52bc-e311-4e67-8dba-aedf8095f9ae

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualRXStepOutput_zero_coarse
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualRZStepOutput_zero_coarse

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26RXDecoderAdapter
open MultiscaleDecoder Coordinates
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (dualFamily S depth).Syndrome i.succ) (hs : sigma.val = 0) :
    (dualStepOutput S depth i sigma).coarse.val = 0 := by
  unfold dualStepOutput
  split
  · exact dualRXStepOutput_zero_coarse S depth i _ sigma hs
  · exact dualRZStepOutput_zero_coarse S depth i _ sigma hs
end QEC.Coding.BDL26TransposedStoppedDecoder
