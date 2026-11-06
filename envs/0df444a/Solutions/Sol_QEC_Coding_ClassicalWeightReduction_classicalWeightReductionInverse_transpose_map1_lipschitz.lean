-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.classicalWeightReductionInverse_transpose_map1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:50:30.35629+00:00
-- url     : https://prove2.me/submissions/a7f392ae-8f7b-47de-b2d5-8cb9f6223e1b

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_HammingWeight_linearMap_le_of_basis
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_classicalWeightReductionInverse_transpose_map1_single_weight_le

set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w
open QEC.Coding.ClassicalWeightReduction
variable {F Check Bit : Type u} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    [CharP F 2] (h : HasNoIsolatedVertices R) (L : Nat)
    (hDegree : ∀ c : Check, Fintype.card (CheckNeighbor R c) ≤ L)
    (x : Word F (WeightReducedBit R)) :
    HammingWeight
        (wordLinearMapTranspose
          (classicalWeightReductionInverseChainMap (F₀ := F) R h).map1 x) ≤
      L * HammingWeight x := by
  exact HammingWeight_linearMap_le_of_basis _ L
    (classicalWeightReductionInverse_transpose_map1_single_weight_le
      (F := F) R h L hDegree) x
end QEC.Coding.ClassicalWeightReduction
