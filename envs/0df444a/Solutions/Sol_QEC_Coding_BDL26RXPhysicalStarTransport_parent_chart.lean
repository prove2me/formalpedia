-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.parent_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:04:05.922016+00:00
-- url     : https://prove2.me/submissions/a09ad4c3-32da-45ef-8507-94b1632b17f4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxDegreeZero_parent


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXPhysicalStarTransport
theorem _root_.solution (x : XCoord S i)
    (v : DoubleCylinderVertex (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.x (rxDegreeZeroEquiv S depth i h ⟨x,v⟩)) =
      some (Vertex.x x) := by
  exact rxDegreeZero_parent S depth i h x v
end QEC.Coding.BDL26RXPhysicalStarTransport
