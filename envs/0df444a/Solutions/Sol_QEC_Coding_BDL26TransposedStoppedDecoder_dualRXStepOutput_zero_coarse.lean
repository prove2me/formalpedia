-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualRXStepOutput_zero_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:36:06.721963+00:00
-- url     : https://prove2.me/submissions/dfa4e302-348f-4b19-884c-8fd0c6a8fa02

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
    (i : StepIndex depth) (h : i.val % 2 = 0) (sigma : (dualFamily S depth).Syndrome i.succ)
    (hs : sigma.val = 0) : (dualRXStepOutput S depth i h sigma).coarse.val = 0 := by
  have hz : (dualRXMaterializedInput S depth i h sigma).val = 0 := by
    change (wordEquiv (dualRXTopZ S depth i h)).symm sigma.val = 0
    exact (congrArg (fun w => (wordEquiv (dualRXTopZ S depth i h)).symm w) hs).trans
      (map_zero _)
  change (BDL26RZDecoderAdapter.presentationOutput (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S
    (dualRXMaterializedInput S depth i h sigma)).coarse.val = 0
  exact BDL26RZDecoderAdapter.presentationOutput_zero_coarse (dualPresentation S i.val)
      (transposeTannerSquareAdmissibleV4 (state S i.val).presentation (state S i.val).admissible) S
    (dualRXMaterializedInput S depth i h sigma) hz
end QEC.Coding.BDL26TransposedStoppedDecoder
