-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualRZStepOutput_zero_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:36:19.851973+00:00
-- url     : https://prove2.me/submissions/d2f62668-2e64-423c-a619-083430bf8f68

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_zero_coarse
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_zero_coarse
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (i : StepIndex depth) (h : ¬i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ)
    (hs : sigma.val = 0) : (dualRZStepOutput S depth i h sigma).coarse.val = 0 := by
  have hz : (dualRZMaterializedInput S depth i h sigma).val = 0 := by
    change (wordEquiv (dualRZTopZ S depth i h)).symm sigma.val = 0
    exact (congrArg (fun w => (wordEquiv (dualRZTopZ S depth i h)).symm w) hs).trans
      (map_zero _)
  change (BDL26RXDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S
    (dualRZMaterializedInput S depth i h sigma)).coarse.val = 0
  exact BDL26RXDecoderAdapter.presentationOutput_zero_coarse (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible)
      (transposeTannerSquareCellularRegular (state S i.val).presentation (state S i.val).regular) S
    (dualRZMaterializedInput S depth i h sigma) hz
end QEC.Coding.BDL26TransposedStoppedDecoder
