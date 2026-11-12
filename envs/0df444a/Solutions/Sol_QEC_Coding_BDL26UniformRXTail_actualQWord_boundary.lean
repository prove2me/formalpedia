-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actualQWord_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:26:05.80179+00:00
-- url     : https://prove2.me/submissions/8e2c9271-a48f-4b42-85a9-0f4613f61c22

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_x_zero
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_boundary
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (tailData S j).contract.rx_local_complexes.cqDelta1 q (actualQWord S j q) =
      restrictWordLinear ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).syndromeRegion q)
        (rxSigmaAfterCx (tailData S j) (lowerSyndrome S j).val) := by
  rw [← cleanedError_boundary]
  exact ((tailData S j).contract.support_decomposition.cqDelta1_restriction_global
    q (cleanedError S j) (cleanedError_x_zero S j)).symm
end QEC.Coding.BDL26UniformRXTail
