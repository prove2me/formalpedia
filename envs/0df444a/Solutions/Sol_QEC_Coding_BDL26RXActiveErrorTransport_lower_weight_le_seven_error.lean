-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.lower_weight_le_seven_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:12:51.104187+00:00
-- url     : https://prove2.me/submissions/f609d91f-61a0-434d-a135-b07d5ed4585d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_active_count_le_weight
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_sharp_le_seven_activeX
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_seven_activeX_le_seven_count
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_lower_weight_le_sharp
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (a b : Upper S depth i) :
    HammingWeight (L S depth i h a b) ≤ 7*HammingWeight (a+b) :=
  (lower_weight_le_sharp S depth i h a b).trans
    ((sharp_le_seven_activeX S depth i h a b).trans
      ((seven_activeX_le_seven_count S depth i h a b).trans
        (Nat.mul_le_mul_left 7 (active_count_le_weight S depth i h (a+b)))))
end QEC.Coding.BDL26RXActiveErrorTransport
