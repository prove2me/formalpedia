-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.uniform_c2_readout_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:22:26.47538+00:00
-- url     : https://prove2.me/submissions/6f678633-4f85-4590-8731-4f27e632e27f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperSyndrome_weight_le_four
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_uniform_c2_weight
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) (hj : 2 ≤ j) :
    LevelTwoHistory.syndromeReadout (indexedDecoderData S (2 * j + 4))
      (BDL26OwnerIncidenceMasks.actualHistory S (2 * j + 2) (upperSyndrome S j))
      ⟨2, by omega⟩ = 0 := by
  apply (HammingWeight_eq_zero_iff _).mp
  have hw := (uniform_c2_weight S j).trans (upperSyndrome_weight_le_four S j)
  have hp : (2 : Nat) ^ 3 ≤ 2 ^ (j + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hp
  nlinarith
end QEC.Coding.BDL26UniformHistoryObstruction
