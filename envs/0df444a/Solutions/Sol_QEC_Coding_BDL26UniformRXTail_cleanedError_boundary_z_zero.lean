-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.cleanedError_boundary_z_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:57:09.886523+00:00
-- url     : https://prove2.me/submissions/0504d47a-1b82-4996-866c-87d90b4ed15a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_boundary
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_syndrome_z_zero
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cx_boundary_z_zero

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
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ (cleanedError S j)
      ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by
  rw [cleanedError_boundary]
  change (lowerSyndrome S j).val _ +
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ
      (cxCorrectionTotal (tailData S j) (lowerSyndrome S j).val) _ = 0
  rw [lower_syndrome_z_zero, actual_cx_boundary_z_zero, zero_add]
end QEC.Coding.BDL26UniformRXTail
