-- Prove2me | solution 1 for QEC.Coding.FiberBundle.weightReductionForwardMap1_basis_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:46:47.751362+00:00
-- url     : https://prove2.me/submissions/3aa5d057-aad6-442f-9997-4a9def51e638

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_horizontal_basis_weight_le_one
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_vertical_primary_weight_le_one
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_vertical_auxiliary_weight_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {L : Nat} (hOne : 1 ≤ L)
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    HammingWeight
        (weightReductionForwardMap1 D h (reducedQubitBasisWord D q)) ≤ L := by
  cases q with
  | inl qi =>
      exact (weightReductionForwardMap1_horizontal_basis_weight_le_one
        D h qi.1 qi.2).trans hOne
  | inr qj =>
      rcases qj with ⟨q, j⟩
      cases q with
      | inl e =>
          exact (weightReductionForwardMap1_vertical_primary_weight_le_one
            D h e j).trans hOne
      | inr a =>
          rcases a with ⟨b, k⟩
          exact (weightReductionForwardMap1_vertical_auxiliary_weight_le
            D h b k j).trans (hBitDegree b)
end QEC.Coding.FiberBundle
