-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_boundary_columns_weightReducedData_le_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:41:39.897204+00:00
-- url     : https://prove2.me/submissions/19363f0a-dba9-46f2-93e0-d20f4250acb8

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_weightReducedData_base_row_le_three
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_weightReducedData_base_col_le_three
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary1_reducedQubitBasisWord_inl_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary1_reducedQubitBasisWord_inr_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary2_reducedQubitBasisWord_inl_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary2_reducedQubitBasisWord_inr_eq

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
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne)
    (hFiberRow : ∀ i : fiberZero,
      HammingWeight (fun j => D.fiberBoundary i j) ≤ 2)
    (hFiberCol : ∀ j : fiberOne,
      HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    HammingWeight
        (boundary1 (weightReducedData D) (reducedQubitBasisWord D q)) +
      HammingWeight
        (wordLinearMapTranspose (boundary2 (weightReducedData D))
          (reducedQubitBasisWord D q)) ≤ 5 := by
  cases q with
  | inl q =>
      rcases q with ⟨b, i⟩
      rw [HammingWeight_boundary1_reducedQubitBasisWord_inl_eq D b i]
      rw [HammingWeight_transpose_boundary2_reducedQubitBasisWord_inl_eq
        D b i]
      have hBase := HammingWeight_weightReducedData_base_col_le_three D b
      have hFiber := hFiberRow i
      omega
  | inr q =>
      rcases q with ⟨a, j⟩
      rw [HammingWeight_boundary1_reducedQubitBasisWord_inr_eq D a j]
      rw [HammingWeight_transpose_boundary2_reducedQubitBasisWord_inr_eq
        D a j]
      have hFiber := hFiberCol j
      have hBase := HammingWeight_weightReducedData_base_row_le_three D a
      omega
end QEC.Coding.FiberBundle
