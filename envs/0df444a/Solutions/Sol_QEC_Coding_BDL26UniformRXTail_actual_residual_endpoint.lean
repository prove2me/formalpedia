-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_residual_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:34:57.236016+00:00
-- url     : https://prove2.me/submissions/a37d53a9-482b-4cb1-847b-8165b4789c77

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_residual_map2
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_diagonal


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    rxSigmaAfterCq (tailData S j) (lowerSyndrome S j).val
      ((tailData S j).induced.zPairEquiv (z,b)).val =
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).castSucc (actualConstants S j) z := by
  rw [actual_residual_map2]
  exact (tailData S j).induced.map2_diagonal _ z b
end QEC.Coding.BDL26UniformRXTail
