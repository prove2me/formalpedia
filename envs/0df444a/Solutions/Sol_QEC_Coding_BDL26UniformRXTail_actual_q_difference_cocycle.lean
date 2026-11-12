-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_q_difference_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:55:31.23458+00:00
-- url     : https://prove2.me/submissions/ad4e0a89-3f9b-4f0a-b15e-3f978ee711ab

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cq_range
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actualQWord_boundary
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cqComponentTotal_local_delta


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    (tailData S j).contract.rx_local_complexes.cqDelta1 q
      (actualQCorrection S j q + actualQWord S j q) = 0 := by
  rw [map_add, actualQWord_boundary]
  have hg := cqComponentTotal_local_delta (tailData S j) (lowerSyndrome S j).val q
    (actual_cq_range S j q)
  rw [show (tailData S j).contract.rx_local_complexes.cqDelta1 q
    (actualQCorrection S j q) = _ from hg]
  exact ZModModule.add_self _
end QEC.Coding.BDL26UniformRXTail
