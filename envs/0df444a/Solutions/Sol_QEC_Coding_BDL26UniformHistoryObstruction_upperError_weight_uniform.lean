-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.upperError_weight_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:22:09.383937+00:00
-- url     : https://prove2.me/submissions/30a1657e-6943-4f5b-a0e0-ae6070077df7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_upperError_weight_le
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    HammingWeight (upperError S j) ≤ 2 * S.ell - 1 := by
  have hd := (state_boundedValence S (2 * j + 3)).2.2 (lowerBasis S j)
  have hm := Nat.mul_le_mul_right S.half hd.2.1
  have he := S.two_half_add_one
  have hw := upperError_weight_le S j
  omega
end QEC.Coding.BDL26UniformHistoryObstruction
