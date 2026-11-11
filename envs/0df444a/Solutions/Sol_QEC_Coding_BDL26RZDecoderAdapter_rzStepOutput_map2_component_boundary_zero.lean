-- Prove2me | solution 1 for QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_map2_component_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:31:08.635041+00:00
-- url     : https://prove2.me/submissions/43b79574-facc-4ce0-9092-4cb3a742ef46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_component_eq
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzData_map2_residual_zero
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrectionComponent_boundary


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
    (sigma : (indexedFamily S depth).Syndrome i.castSucc)
    (j : Fin (rzStepOutput S depth i h
      (embeddedSyndrome S depth i sigma)).localComponents.length) :
    (rzStepOutput S depth i h (embeddedSyndrome S depth i sigma)).componentCoboundaryAt j = 0 := by
  rw [AssemblyStepOutput.componentCoboundaryAt_eq, rzStepOutput_component_eq]
  funext p
  rw [localCorrectionComponent_boundary]
  exact congrFun (rzData_map2_residual_zero S depth i h sigma.val _) p
end QEC.Coding.BDL26RZDecoderAdapter
