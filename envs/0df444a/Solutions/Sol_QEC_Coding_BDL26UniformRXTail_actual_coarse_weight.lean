-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_coarse_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:31:23.761982+00:00
-- url     : https://prove2.me/submissions/2786323a-a7e4-4142-ba8a-3b6f10b49dcf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_coarse_equation
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_weight


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
      (tailIndex j).castSucc (actualConstants S j)) ≤ HammingWeight (lowerSyndrome S j).val := by
  rw [← actual_coarse_equation]
  exact rxStepOutput_weight S (2 * j + 4) (tailIndex j) (tailIndex_even j) (lowerSyndrome S j)
end QEC.Coding.BDL26UniformRXTail
