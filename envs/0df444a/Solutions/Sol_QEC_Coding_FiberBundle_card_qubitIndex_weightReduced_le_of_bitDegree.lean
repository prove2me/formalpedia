-- Prove2me | solution 1 for QEC.Coding.FiberBundle.card_qubitIndex_weightReduced_le_of_bitDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:52:45.729484+00:00
-- url     : https://prove2.me/submissions/4d819f7f-7adf-4f05-99d0-1461e9b97596

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_card_incidence_le_card_baseOne_mul
import Theorems.Thm_QEC_Coding_FiberBundle_card_qubitIndex_weightReduced_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u v
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {L : Nat}
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L) :
    Fintype.card
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) ≤
      2 * (Fintype.card baseOne * L) *
        (Fintype.card fiberZero + Fintype.card fiberOne) := by
  exact (card_qubitIndex_weightReduced_le D).trans
    (Nat.mul_le_mul_right
      (Fintype.card fiberZero + Fintype.card fiberOne)
      (Nat.mul_le_mul_left 2
        (card_incidence_le_card_baseOne_mul D hBitDegree)))
end QEC.Coding.FiberBundle
