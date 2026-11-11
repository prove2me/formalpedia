-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.raw_local_edge_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:49:21.169119+00:00
-- url     : https://prove2.me/submissions/ee417cfb-b61e-4a2a-8d7c-9adb8560424b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport

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
include odd
namespace QEC.Coding.BDL26RZPhysicalStarTransport
theorem _root_.solution (z z' : (Old S depth i).Z)
    (e : ZDoubleCylinderEdge (Old S depth i) z S)
    (v : ZDoubleCylinderVertex (Old S depth i) z' S)
    (hi : rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
      (.inl ⟨z,e⟩) ⟨z',v⟩=true) : z'=z := by
  change decide (∃ he : z'=z,
    doubleCylinderEdgeVertexMatrix (transposePresentation (Old S depth i)) z S (he ▸ v) e=1)=true at hi
  exact (of_decide_eq_true hi).choose
end QEC.Coding.BDL26RZPhysicalStarTransport
