-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.gradient_potential_boundary_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:24:50.06886+00:00
-- url     : https://prove2.me/submissions/f8597156-455b-45f2-9016-30ec76d0f454

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_boundary_x
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradient_updated_x
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_boundaryGradient_nonzero
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXXStarTransport
theorem _root_.solution (x : XCoord S i) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary0 i.succ
      (potential S depth i h x a (a+gradientError S depth i h x)) ≠ 0 := by
  intro hz
  have he := potential_boundary_x S depth i h x a (a+gradientError S depth i h x)
  rw [hz,map_zero,gradient_updated_x] at he
  exact boundaryGradient_nonzero S depth i h x he.symm
end QEC.Coding.BDL26RXXStarTransport
