-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.retained_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:28:20.435684+00:00
-- url     : https://prove2.me/submissions/68128640-1832-4969-9137-ee713a06807a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_endpoint_transport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
theorem _root_.solution (above : 3 ≤ i.val) (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    let q := retainedQ S depth i
    let e := retainedEdge S depth i
    let u := upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (edgeEndpointQ S depth i odd q e c)
    ∃ p : Potential S depth i, Pullback S depth i odd {q} (Coordinates.neighborZ (Old S depth i) {q}) a b p ∧
      parent S (i.val+1) (Vertex.x u)=none ∧
      lowerError S depth i odd a b=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ∧
      lowerError S depth i odd a b≠0 ∧ HammingWeight (lowerError S depth i odd a b) ≤ 1 :=
  endpoint_transport S depth i odd above _ _ c a
end QEC.Coding.BDL26RZPhysicalXStarTransport
