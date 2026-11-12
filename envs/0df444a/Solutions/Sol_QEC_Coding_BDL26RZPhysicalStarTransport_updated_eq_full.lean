-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalStarTransport.updated_eq_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:17:47.0492+00:00
-- url     : https://prove2.me/submissions/f9e025b9-2ff0-479a-9fce-5ee315bb486c

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
namespace QEC.Coding.BDL26RZPhysicalStarTransport
theorem _root_.solution (a b : Upper S depth i) :
    updated S depth i odd a b=a+b+(run S depth i odd a).correction+
      (run S depth i odd b).correction := rfl
end QEC.Coding.BDL26RZPhysicalStarTransport
