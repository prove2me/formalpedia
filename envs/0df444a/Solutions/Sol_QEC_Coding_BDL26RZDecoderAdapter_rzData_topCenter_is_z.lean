-- Prove2me | solution 1 for QEC.Coding.BDL26RZDecoderAdapter.rzData_topCenter_is_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:15:34.815661+00:00
-- url     : https://prove2.me/submissions/4a1661eb-6957-4ba4-a151-3d20b54b4be0

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
    (p : FamilyZ S depth i.succ) :
    ∃ z, (rzData S depth i h).topCenter p = Vertex.z z := by
  have hg := transportEndpoint_property _ _ _
    (congrArg ConstructionState.presentation (stateSuccRZ S depth i h))
    (actualEndpoint (state S i.val).presentation (state S i.val).admissible S)
    (fun U G => ∀ q : U.Z, ∃ z, G.topCenter q = Vertex.z z)
    (by intro q; exact ⟨q.1, rfl⟩)
  exact hg p
end QEC.Coding.BDL26RZDecoderAdapter
