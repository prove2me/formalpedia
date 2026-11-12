-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actual_residual_auxiliary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:35:00.576193+00:00
-- url     : https://prove2.me/submissions/23ae5cea-beb1-4762-be2d-1d5567f90bb7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_residual_map2
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_auxiliary_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat)
    (p : FamilyZ S (2 * j + 4) (tailIndex j).succ)
    (hp : p ∉ (tailData S j).induced.zSector) :
    rxSigmaAfterCq (tailData S j) (lowerSyndrome S j).val p = 0 := by
  rw [actual_residual_map2]
  exact (tailData S j).induced.map2_auxiliary_zero _ p hp
end QEC.Coding.BDL26UniformRXTail
