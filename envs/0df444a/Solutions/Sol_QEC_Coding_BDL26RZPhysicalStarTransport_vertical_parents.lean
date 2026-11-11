-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.vertical_parents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:40:30.709986+00:00
-- url     : https://prove2.me/submissions/287bcded-24c1-44e6-80f8-a07ec7a00a72

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_centre_parent
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_local_edge_parent_none
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_vertical_incident

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalStarTransport
theorem _root_.solution (z : (Old S depth i).Z)
    (v : SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) z S) :
    (state S (i.val+1)).presentation.qz (verticalPhysical S depth i odd z v)
      (verticalCentre S depth i odd z v)=true ∧
    parent S (i.val+1) (Vertex.q (verticalPhysical S depth i odd z v))=none ∧
    parent S (i.val+1) (Vertex.z (verticalCentre S depth i odd z v))=some (Vertex.z z) :=
  ⟨vertical_incident S depth i odd z v,local_edge_parent_none S depth i odd z _,
    centre_parent S depth i odd z _⟩
end QEC.Coding.BDL26RZPhysicalStarTransport
