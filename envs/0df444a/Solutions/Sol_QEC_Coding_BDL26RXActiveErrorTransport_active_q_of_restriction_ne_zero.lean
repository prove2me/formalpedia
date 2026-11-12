-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.active_q_of_restriction_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:50:54.418447+00:00
-- url     : https://prove2.me/submissions/f51d72c1-7b18-4d8d-b37e-11c86fe68a07

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_inactive_q_iff

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
theorem _root_.solution (E : Upper S depth i) (q : QCoord S i)
    (hn : restrictWordLinear ((rxLq S depth i h).correctionRegion q) E≠0) :
    q ∈ activeQ S depth i h E := by
  by_contra hq
  exact hn ((inactive_q_iff S depth i h E q).mp hq)
end QEC.Coding.BDL26RXActiveErrorTransport
