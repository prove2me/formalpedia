-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_coarse_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:25:58.070167+00:00
-- url     : https://prove2.me/submissions/4cde94bb-de87-4df6-9434-fe883fe7aae0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_residual_map2
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_coarse
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_coarseProjection_eq_of_map2
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat) :
    (rxStepOutput S (2 * j + 4) (tailIndex j) (tailIndex_even j) (lowerSyndrome S j)).coarse.val =
      (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).castSucc (actualConstants S j) := by
  rw [rxStepOutput_coarse, rxCoarseWord]
  exact coarseProjection_eq_of_map2 (tailData S j) _ _ (actual_residual_map2 S j).symm
end QEC.Coding.BDL26UniformRXTail
