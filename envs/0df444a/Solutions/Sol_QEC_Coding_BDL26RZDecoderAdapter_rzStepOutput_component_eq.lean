-- Prove2me | solution 1 for QEC.Coding.BDL26RZDecoderAdapter.rzStepOutput_component_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:52:40.896248+00:00
-- url     : https://prove2.me/submissions/59c7d46e-6bbc-4522-a149-4843fec81b7a

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
    (rzStepOutput S depth i h sigma).componentAt j =
      localCorrectionComponent (rzData S depth i h)
        (rzData_localTopCohomology S depth i h)
        (componentOwner S depth i h sigma j) sigma.val := by
  change ((Finset.univ : Finset ((state S i.val).presentation.Z)).toList.map
    (fun z => localCorrectionComponent (rzData S depth i h)
      (rzData_localTopCohomology S depth i h) z sigma.val)).get j = _
  change ((Finset.univ : Finset ((state S i.val).presentation.Z)).toList.map
    (fun z => localCorrectionComponent (rzData S depth i h)
      (rzData_localTopCohomology S depth i h) z sigma.val))[j.val] = _
  rw [List.getElem_map]
  rfl
end QEC.Coding.BDL26RZDecoderAdapter
