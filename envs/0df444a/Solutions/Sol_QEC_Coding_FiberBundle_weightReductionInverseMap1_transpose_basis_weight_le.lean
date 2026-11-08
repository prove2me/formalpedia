-- Prove2me | solution 1 for QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_basis_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:49:16.904326+00:00
-- url     : https://prove2.me/submissions/954d2a55-d819-4fbd-bb04-d5067622c985

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_horizontal_primary_weight_le_one
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_horizontal_auxiliary_weight_le
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_vertical_primary_weight_le_one
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionInverseMap1_transpose_vertical_auxiliary_weight_eq_zero

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
    (hCheckDegree : ∀ c : baseZero,
      Fintype.card (ClassicalWeightReduction.CheckNeighbor R c) ≤ L)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (weightReductionInverseMap1 D h)
          (reducedQubitBasisWord D q)) ≤ L := by
  cases q with
  | inl qi =>
      rcases qi with ⟨q, k⟩
      cases q with
      | inl e =>
          exact
            (weightReductionInverseMap1_transpose_horizontal_primary_weight_le_one
              D h e k).trans hOne
      | inr a =>
          exact
            (weightReductionInverseMap1_transpose_horizontal_auxiliary_weight_le
              D h a k).trans (hCheckDegree a.1)
  | inr qj =>
      rcases qj with ⟨q, k⟩
      cases q with
      | inl e =>
          exact
            (weightReductionInverseMap1_transpose_vertical_primary_weight_le_one
              D h e k).trans hOne
      | inr a =>
          rw [weightReductionInverseMap1_transpose_vertical_auxiliary_weight_eq_zero]
          omega
end QEC.Coding.FiberBundle
