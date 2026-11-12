-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_cq_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:50:20.453204+00:00
-- url     : https://prove2.me/submissions/fcf6d371-387b-492e-9318-91bd4b1827f8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cq_range
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actualQWord_boundary
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cqComponentTotal_local_flow_weight


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
    HammingWeight ((tailData S j).contract.support_decomposition.cqFlow q
      (restrictWordLinear ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion q)
        (cqComponentTotal (tailData S j) (lowerSyndrome S j).val q))) ≤
      HammingWeight ((tailData S j).contract.rx_local_complexes.cqDelta1 q (actualQWord S j q)) := by
  rw [actualQWord_boundary]
  exact cqComponentTotal_local_flow_weight _ _ _ (actual_cq_range S j q)
end QEC.Coding.BDL26UniformRXTail
