-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_q_difference_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:02:43.502527+00:00
-- url     : https://prove2.me/submissions/3c15837a-954d-4316-bd80-374bc7c2cee4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_q_difference_cocycle
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxQ_kernel_constant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q)
    (v : QDoubleCylinderVertex (state S (2 * j + 2)).presentation q S) :
    let p := rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q v
    actualQCorrection S j q p + actualQWord S j q p = actualConstants S j q :=
  rxQ_kernel_constant S (2 * j + 4) (tailIndex j) (tailIndex_even j) q
    (actualQCorrection S j q + actualQWord S j q) (actual_q_difference_cocycle S j q) v
end QEC.Coding.BDL26UniformRXTail
