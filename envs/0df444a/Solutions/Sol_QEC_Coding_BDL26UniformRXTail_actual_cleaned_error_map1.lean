-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_cleaned_error_map1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:12:43.628781+00:00
-- url     : https://prove2.me/submissions/c4be1511-2fa5-45b4-9d82-c4e2aacccea6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_q_decomposition
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_q_difference_value
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cq_correction_decomposition
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxMap1_constant_Q
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat) :
    cleanedError S j + cqCorrectionTotal (tailData S j) (lowerSyndrome S j).val =
      ((indexedDecoderData S (2 * j + 4)).rxMap (tailIndex j)).map1 (actualConstants S j) := by
  rw [cleanedError_q_decomposition, actual_cq_correction_decomposition,
    rxMap1_constant_Q S (2 * j + 4) (tailIndex j) (tailIndex_even j),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [← map_add]
  congr 1
  funext p
  obtain ⟨v, rfl⟩ := (rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q).surjective p
  exact (add_comm _ _).trans (actual_q_difference_value S j q v)
end QEC.Coding.BDL26UniformRXTail
