-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_boundary_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:07:24.576472+00:00
-- url     : https://prove2.me/submissions/5ce532e8-2570-4997-a55c-fbfcb432484c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_gradient_pair_shift_active
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_boundary_nonzero


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (x0 x1 : XCoord S i) (hn : x0≠x1) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary0 i.succ
      (Phi S depth i h a (a+(gradientError S depth i h x0+gradientError S depth i h x1)))≠0 := by
  unfold Phi
  rw [(gradient_pair_shift_active S depth i h x0 x1 hn a).1]
  exact BDL26RXFiniteBlockTransport.gradient_pair_boundary_nonzero S depth i h x0 x1 hn a
end QEC.Coding.BDL26RXActiveErrorTransport
