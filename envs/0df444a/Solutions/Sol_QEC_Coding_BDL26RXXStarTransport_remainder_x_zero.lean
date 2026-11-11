-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.remainder_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:28:44.201187+00:00
-- url     : https://prove2.me/submissions/2850fdb8-95ce-4c39-9bd9-d806c89222ec

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_boundary_x
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_boundary_other_x
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_updated_other_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self


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
theorem _root_.solution (x y : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (remainder S depth i h x a b)=0 := by
  rw [remainder,map_add]
  by_cases hy : y=x
  · subst y
    rw [potential_boundary_x,word_add_self]
  · rw [updated_other_x_zero S depth i h x y hy a b he,
      potential_boundary_other_x S depth i h x y hy,zero_add]
end QEC.Coding.BDL26RXXStarTransport
