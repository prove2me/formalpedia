-- Prove2me | solution 1 for QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_map2_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:03:21.580424+00:00
-- url     : https://prove2.me/submissions/ca97ad35-9171-4b73-a0fa-60b7da40d6d8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_coarse_apply
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_topParity_rzMap_map2


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
    (sigma : (indexedFamily S depth).Syndrome i.castSucc) :
    (rzStepOutput S depth i h (embeddedSyndrome S depth i sigma)).coarse = sigma := by
  apply Subtype.ext
  funext z
  rw [rzStepOutput_coarse_apply]
  change topParity (rzData S depth i h)
    (((indexedDecoderData S depth).selectedMap i).map2 sigma.val) z = sigma.val z
  rw [selectedMap_eq]
  exact congrFun (topParity_rzMap_map2 (rzData S depth i h) sigma.val) z
end QEC.Coding.BDL26RZDecoderAdapter
