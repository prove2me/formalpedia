-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_gradient_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:29:20.918673+00:00
-- url     : https://prove2.me/submissions/14ce7c88-d94a-4e5d-87da-571c0f84b760

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_gradient_coordinates
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1QEdge_delta0_end
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1QEdge_delta0_start


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
theorem _root_.solution (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) :
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))
      (.inr ⟨q,qDoubleCylinderEdgeStart (transposePresentation (Old S depth i)) q S e⟩)=1 ∧
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))
      (.inr ⟨q,qDoubleCylinderEdgeEnd (transposePresentation (Old S depth i)) q S e⟩)=1 := by
  constructor
  · rw [gradient_coordinates]
    exact rzMap1QEdge_delta0_start _ _ _ _ _
  · rw [gradient_coordinates]
    exact rzMap1QEdge_delta0_end _ _ _ _ _
end QEC.Coding.BDL26RZPhysicalXStarTransport
