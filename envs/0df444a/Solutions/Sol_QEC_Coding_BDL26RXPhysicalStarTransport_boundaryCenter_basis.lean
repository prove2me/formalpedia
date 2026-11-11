-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:16:22.41546+00:00
-- url     : https://prove2.me/submissions/80d412c4-b25c-417b-8ccf-cd239112414d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lift_singleton_eq_basis
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution (x : XCoord S i) :
    canonicalBasisWord (boundaryCenter S depth i h x)=
      (rxContract S depth i h).support_decomposition.cxLift0 x (boundarySingleton S depth i x) :=
  (lift_singleton_eq_basis S depth i h x (0,(boundaryVertex S depth i x).val)).symm
end QEC.Coding.BDL26RXPhysicalStarTransport
