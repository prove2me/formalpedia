-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.active_x_of_restriction_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:47:30.688105+00:00
-- url     : https://prove2.me/submissions/1d580a12-9f38-4e96-9dfa-4c13393b5d63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_inactive_x_iff

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
theorem _root_.solution (E : Upper S depth i) (x : XCoord S i)
    (hn : restrictWordLinear ((rxLx S depth i h).correctionRegion x) E≠0) :
    x ∈ activeX S depth i h E := by
  by_contra hx
  exact hn ((inactive_x_iff S depth i h E x).mp hx)
end QEC.Coding.BDL26RXActiveErrorTransport
