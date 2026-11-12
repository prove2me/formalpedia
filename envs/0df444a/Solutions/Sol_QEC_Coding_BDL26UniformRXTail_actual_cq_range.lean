-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_cq_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:11:34.43618+00:00
-- url     : https://prove2.me/submissions/3c203a9c-1994-4140-85ab-1536e8c9fd16

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_x_zero
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_boundary
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXConstructionContractSlice_cq_local_ranges_of_error


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
    CqLocalRangeAt (tailData S j) (lowerSyndrome S j).val q := by
  have h : restrictWordLinear
      ((rxLq S (2*j+4) (tailIndex j) (tailIndex_even j)).syndromeRegion q)
      ((indexedFamily S (2*j+4)).coboundary1 (tailIndex j).succ (cleanedError S j)) ∈
      LinearMap.range ((tailData S j).contract.rx_local_complexes.cqDelta1 q) :=
    (tailData S j).contract.cq_local_ranges_of_error
      (cleanedError S j) (cleanedError_x_zero S j) q
  rw [cleanedError_boundary] at h
  exact h
end QEC.Coding.BDL26UniformRXTail
