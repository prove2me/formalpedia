-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.raw_q_vertex_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:34:17.771599+00:00
-- url     : https://prove2.me/submissions/ad7f47cb-7bea-498c-8f8f-e5227ed1eef2

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
theorem _root_.solution (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S)
    (w : ZDoubleCylinderVertex (Old S depth i) z S)
    (hi : rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
      (.inr ⟨q,v⟩) ⟨z,w⟩=true) : (Old S depth i).qz q z=true := by
  change decide (∃ hqz : (Old S depth i).qz q z=true,
    qToZDoubleCylinderVertex (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible
      q z hqz S v=w)=true at hi
  exact (of_decide_eq_true hi).choose
end QEC.Coding.BDL26RZPhysicalStarTransport
