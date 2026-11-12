-- Prove2me | solution 1 for QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_owner_snapshot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:14:57.256325+00:00
-- url     : https://prove2.me/submissions/4f048e3e-61ae-4990-b66e-f080991e00fe

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
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (j : Fin (rzStepOutput S depth i h sigma).localComponents.length) :
    ((rzStepOutput_ownerLabels S depth i h sigma).label j).owner =
        some (.z (componentOwner S depth i h sigma j)) ∧
    ((rzStepOutput_ownerLabels S depth i h sigma).label j).correctionSupport =
        (rzStepOutput S depth i h sigma).componentSupportAt j ∧
    ((rzStepOutput_ownerLabels S depth i h sigma).label j).coboundarySupport =
        hammingSupport ((rzStepOutput S depth i h sigma).componentCoboundaryAt j) :=
  ⟨rfl, rfl, rfl⟩
end QEC.Coding.BDL26RZDecoderAdapter
