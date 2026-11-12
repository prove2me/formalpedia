-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.retained_vertical_parents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:18:45.483785+00:00
-- url     : https://prove2.me/submissions/58b87a34-46aa-4600-b1ce-3311bfbcaa11

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_vertical_parents

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
theorem _root_.solution :
    (state S (i.val+1)).presentation.qz
      (verticalPhysical S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i))
      (verticalCentre S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i))=true ∧
    parent S (i.val+1) (Vertex.q
      (verticalPhysical S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i)))=none ∧
    parent S (i.val+1) (Vertex.z
      (verticalCentre S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i)))=
        some (Vertex.z (retainedZ S depth i)) :=
  vertical_parents S depth i odd _ _
end QEC.Coding.BDL26RZPhysicalStarTransport
