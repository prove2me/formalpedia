-- Prove2me | solution 1 for QEC.Coding.FiberBundle.card_qubitIndex_weightReduced_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:50:13.31621+00:00
-- url     : https://prove2.me/submissions/4e004f90-7f2a-453f-9504-324362fa0080

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_card_weightReducedCheck_le_two_mul_incidence
import Theorems.Thm_QEC_Coding_FiberBundle_card_weightReducedBit_le_two_mul_incidence
import Theorems.Thm_QEC_Coding_FiberBundle_card_qubitIndex


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
theorem _root_.solution :
    Fintype.card
        (QubitIndex
          (ClassicalWeightReduction.WeightReducedCheck R)
          (ClassicalWeightReduction.WeightReducedBit R)
          fiberZero fiberOne) ≤
      2 * Fintype.card (ClassicalWeightReduction.Incidence R) *
        (Fintype.card fiberZero + Fintype.card fiberOne) := by
  rw [card_qubitIndex]
  have hBit := card_weightReducedBit_le_two_mul_incidence D
  have hCheck := card_weightReducedCheck_le_two_mul_incidence D
  nlinarith
end QEC.Coding.FiberBundle
