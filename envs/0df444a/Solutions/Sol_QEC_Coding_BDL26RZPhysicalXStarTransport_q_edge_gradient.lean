-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_gradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:28:34.676839+00:00
-- url     : https://prove2.me/submissions/8a23b702-b8e7-4c22-9dd9-139bf9d400c4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_read0_basis
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_gradient_coordinates
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_delta0_coordinates
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzMap1QEdge_delta0_canonicalBasis


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
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) (a : Upper S depth i) :
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))=
      rzMap1QEdgeDelta0BasisImage (Old S depth i) (state S i.val).admissible S q e ∧
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))=0 := by
  constructor
  · rw [gradient,delta0_coordinates,read0_basis]
    exact rzMap1QEdge_delta0_canonicalBasis (Old S depth i) (state S i.val).admissible S q e
  · rw [lower_gradient_coordinates]
    exact rzQParity_qEdge_coboundary (Old S depth i) (state S i.val).admissible S q e
end QEC.Coding.BDL26RZPhysicalXStarTransport
