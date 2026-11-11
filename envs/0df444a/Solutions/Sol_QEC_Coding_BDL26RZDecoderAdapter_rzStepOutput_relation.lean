-- Prove2me | solution 1 for QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:14:17.289016+00:00
-- url     : https://prove2.me/submissions/e39232af-5e20-4483-9dbd-0b0d3a4ca717

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementSupport BDL26RZConcreteParity BDL26LevelTwoDistance
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open BDL26AlternatingCochain BDL26ReplacementCochainMaps
open scoped Classical BigOperators
universe u
attribute [local instance] QEC.Coding.BDL26RZDecoderAdapter.rzQDecEq
attribute [local instance] QEC.Coding.BDL26RZDecoderAdapter.rzZDecEq
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RZDecoderAdapter
theorem _root_.solution (h : ¬i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Syndrome i.succ) :
    sigma.val = (indexedFamily S depth).coboundary1 i.succ
      (rzStepOutput S depth i h sigma).correction +
      ((indexedDecoderData S depth).selectedMap i).map2
        (rzStepOutput S depth i h sigma).coarse.val :=
  (rzStepOutput S depth i h sigma).relation
end QEC.Coding.BDL26RZDecoderAdapter
