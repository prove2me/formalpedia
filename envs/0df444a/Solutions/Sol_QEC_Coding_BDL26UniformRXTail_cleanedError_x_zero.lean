-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.cleanedError_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:05:51.91921+00:00
-- url     : https://prove2.me/submissions/00b8ac3c-1766-4583-b5db-1c83130d9180

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actualPotential_boundary

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
    restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
      (cleanedError S j) = 0 := by
  have hl : restrictWordLinear
      ((rxLx S (2*j+4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
      ((indexedFamily S (2*j+4)).coboundary0 (tailIndex j).succ (actualLift S j)) =
      (tailData S j).contract.rx_local_complexes.cxDelta0 x (actualPotential S j x) :=
    (tailData S j).contract.support_decomposition.cxDelta0_sum_decomposition (actualPotential S j) x
  rw [cleanedError, map_add, hl, actualPotential_boundary]
  ext p
  exact ZModModule.add_self _
end QEC.Coding.BDL26UniformRXTail
