-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.boundaryGradient_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:50:42.173656+00:00
-- url     : https://prove2.me/submissions/f0f7bf12-c600-4b24-978e-8f90d27d461e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_boundarySingleton_vertical
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxCxDelta0_eq_zero_iff_raw


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
theorem _root_.solution (x : XCoord S i) : boundaryGradient S depth i h x ≠ 0 := by
  intro hz
  have hr := (rxCxDelta0_eq_zero_iff_raw S depth i h x (boundarySingleton S depth i x)).mp hz
  have he := congrFun hr (Sum.inr (boundaryVertex S depth i x))
  rw [boundarySingleton_vertical] at he
  exact one_ne_zero he
end QEC.Coding.BDL26RXXStarTransport
