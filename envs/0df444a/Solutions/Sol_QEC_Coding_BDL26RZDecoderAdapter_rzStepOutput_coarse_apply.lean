-- Prove2me | solution 1 for QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_coarse_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:58:31.355267+00:00
-- url     : https://prove2.me/submissions/e5a59fbd-937f-44b8-94be-5842108f4375

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_AuditedLeafAdapters_rzOutput_coarse_apply


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
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (z : (state S i.val).presentation.Z) :
    (rzStepOutput S depth i h sigma).coarse.val z =
      ∑ p ∈ (rzData S depth i h).coarseRegion z, sigma.val p :=
  AuditedLeafAdapters.rzOutput_coarse_apply _ _ _ _ _ _
end QEC.Coding.BDL26RZDecoderAdapter
