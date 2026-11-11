-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_phi_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:03:18.7175+00:00
-- url     : https://prove2.me/submissions/fd817e88-c5a5-40d8-8693-c15456fecc46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_boundary_nonzero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXFiniteBlockTransport
theorem _root_.solution (x0 x1 : XCoord S i) (hne : x0≠x1)
    (a : Upper S depth i) :
    Phi S depth i h {x0,x1} a
      (a+(gradientError S depth i h x0+gradientError S depth i h x1)) ≠ 0 := by
  intro hz
  apply gradient_pair_boundary_nonzero S depth i h x0 x1 hne a
  rw [hz,map_zero]
end QEC.Coding.BDL26RXFiniteBlockTransport
