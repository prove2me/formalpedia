-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.HammingWeight_le_restrictedHammingWeight_add_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:41.124301+00:00
-- url     : https://prove2.me/submissions/d3dbee69-d392-4cc3-bcc3-e40defb4fbdd

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (A : Finset W) (x : Word F W) :
    HammingWeight x ≤
      restrictedHammingWeight A x + (Fintype.card W - A.card) := by
  classical
  unfold HammingWeight hammingSupport restrictedHammingWeight
  let S := Finset.univ.filter fun i => x i ≠ 0
  have hSplit : S = (S ∩ A) ∪ (S \ A) := by
    ext i
    by_cases hiA : i ∈ A <;> simp [hiA]
  calc
    S.card = ((S ∩ A) ∪ (S \ A)).card := congrArg Finset.card hSplit
    _ ≤ (S ∩ A).card + (S \ A).card := Finset.card_union_le _ _
    _ ≤ (S ∩ A).card + (Finset.univ \ A).card := by
      apply Nat.add_le_add_left
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_sdiff] at hi ⊢
      exact ⟨Finset.mem_univ i, hi.2⟩
    _ = restrictedHammingWeight A x + (Fintype.card W - A.card) := by
      have hInter : (S ∩ A).card = restrictedHammingWeight A x := by
        have hFilter : S ∩ A = A.filter (fun i => x i ≠ 0) := by
          ext i
          simp [S, and_comm]
        rw [hFilter, Finset.card_filter]
        unfold restrictedHammingWeight
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hxi : x i = 0 <;> simp [hxi]
      rw [hInter, Finset.card_sdiff_of_subset (Finset.subset_univ A)]
      simp
end QEC.Coding.ProductExpansion
