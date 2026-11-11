-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_gradient_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:50:11.283647+00:00
-- url     : https://prove2.me/submissions/36f44df7-a16d-435e-b5ba-2c18411d7cf0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_boundaryCenter_gradient_restriction
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_boundaryGradient_nonzero
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
    gradient S depth i (boundaryCenter S depth i h x)≠0 := by
  intro hz
  have hr := boundaryCenter_gradient_restriction S depth i h x
  rw [hz,map_zero] at hr
  exact boundaryGradient_nonzero S depth i h x hr.symm
end QEC.Coding.BDL26RXPhysicalStarTransport
