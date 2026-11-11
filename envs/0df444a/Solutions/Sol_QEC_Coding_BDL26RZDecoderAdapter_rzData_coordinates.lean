-- Prove2me | solution 1 for QEC.Coding.BDL26RZDecoderAdapter.rzData_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:58:21.216192+00:00
-- url     : https://prove2.me/submissions/5092e2c0-e3e5-4423-bc8b-9d2e6a6a1e87

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
theorem _root_.solution (h : ¬i.val % 2 = 0) :
    HEq (rzData S depth i h).coarseRegion
      (blockRegion (state S i.val).presentation S) ∧
    HEq (rzData S depth i h).correctionRegion
      (BDL26RZSupportedBoundary.correctionRegion (state S i.val).presentation S) ∧
    HEq (rzData S depth i h).correctionOwner
      (blockCorrectionOwner (state S i.val).presentation S) ∧
    HEq (rzData S depth i h).induced.correctionProjection
      (rzQParity (state S i.val).presentation S) := by
  have hf := transportEndpoint_fields _ _ _
    (congrArg ConstructionState.presentation (stateSuccRZ S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible S)
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
end QEC.Coding.BDL26RZDecoderAdapter
