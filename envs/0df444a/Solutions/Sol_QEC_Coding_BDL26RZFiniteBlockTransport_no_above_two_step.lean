-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.no_above_two_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:15:54.980231+00:00
-- url     : https://prove2.me/submissions/b40ad0d8-c612-4f35-8355-d953a69ff2af

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)
namespace QEC.Coding.BDL26RZFiniteBlockTransport
theorem _root_.solution (hdepth : depth ≤ 2) : ¬ 2 ≤ i.val := by omega
end QEC.Coding.BDL26RZFiniteBlockTransport
