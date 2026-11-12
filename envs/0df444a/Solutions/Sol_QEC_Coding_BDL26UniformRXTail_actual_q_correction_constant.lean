-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_q_correction_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:12:59.691373+00:00
-- url     : https://prove2.me/submissions/ef128f6d-5979-4b17-ae41-0b0c3e345385

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_q_difference_value
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    actualQCorrection S j q = actualQWord S j q + (fun _ => actualConstants S j q) := by
  funext p
  obtain ⟨v,rfl⟩ := (rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q).surjective p
  have hv := actual_q_difference_value S j q v
  have ht := congrArg (fun t => t + actualQWord S j q
    (rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q v)) hv
  rw [add_assoc, ZModModule.add_self, add_zero] at ht
  exact ht.trans (add_comm _ _)
end QEC.Coding.BDL26UniformRXTail
