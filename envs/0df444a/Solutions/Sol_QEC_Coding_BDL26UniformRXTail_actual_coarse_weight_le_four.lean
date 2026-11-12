-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_coarse_weight_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:34:11.823694+00:00
-- url     : https://prove2.me/submissions/4bedc32f-ab5e-4956-8003-ead0500dc259

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_coarse_weight
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_syndrome_weight_le_four
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
    2 * HammingWeight ((indexedFamily S (2 * j + 4)).coboundary1
      (tailIndex j).castSucc (actualConstants S j)) ≤ 4 :=
  (actual_coarse_weight S j).trans (lower_syndrome_weight_le_four S j)
end QEC.Coding.BDL26UniformRXTail
