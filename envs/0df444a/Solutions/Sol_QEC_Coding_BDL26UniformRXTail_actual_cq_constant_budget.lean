-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_cq_constant_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:35:03.826266+00:00
-- url     : https://prove2.me/submissions/e4758097-6d0c-4082-bd9b-fffc3483ffbd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cq_budget
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_q_correction_constant

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
      (actualQWord S j q + (fun _ => actualConstants S j q))) ≤
    HammingWeight ((tailData S j).contract.rx_local_complexes.cqDelta1 q (actualQWord S j q)) := by
  rw [← actual_q_correction_constant]
  exact actual_cq_budget S j q
end QEC.Coding.BDL26UniformRXTail
