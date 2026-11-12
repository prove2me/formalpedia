-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_cx_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:33:45.472386+00:00
-- url     : https://prove2.me/submissions/cadbf8b4-cee5-4b16-99e7-919d141a3b90

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cxComponentTotal_local_flow_weight
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXConstructionContractSlice_cx_local_ranges_of_syndrome


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat)
    (x : (state S (2 * j + 2)).presentation.X) :
    HammingWeight ((tailData S j).contract.support_decomposition.cxFlow x
      (restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
        (cxComponentTotal (tailData S j) (lowerSyndrome S j).val x))) ≤
      HammingWeight ((tailData S j).contract.rx_local_complexes.cxDelta1 x
        (restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
          (lowerError S j))) := by
  rw [← (tailData S j).contract.support_decomposition.cxDelta1_restriction_global]
  exact cxComponentTotal_local_flow_weight _ _ _
    ((tailData S j).contract.cx_local_ranges_of_syndrome (lowerSyndrome S j) x)
end QEC.Coding.BDL26UniformRXTail
