-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.rectangle_weight_ge_escaping_columns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:19.405201+00:00
-- url     : https://prove2.me/submissions/962798e9-ac83-44bd-8991-82b82fc9a7e2

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_eq_sum_column_restrictedHammingWeight
import Theorems.Thm_QEC_Coding_ProductExpansion_escaping_column_restrictedWeight_ge_threshold
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W]
    (h' : Matrix R' W F) (x : Matrix W W F) (A B : Finset W) (d : Nat)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
    (hMin : ∀ D : Finset (Word F W),
      D.card = (h' * x).rank →
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
      generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) :
    d * ((columnsOutsideSyndromeSpan h' x (lightGenerators A C d)) ∩ B).card ≤
      6 * C.card * restrictedWeight x A B := by
  classical
  let E := columnsOutsideSyndromeSpan h' x (lightGenerators A C d)
  let S := E ∩ B
  have hEach (j : W) (hj : j ∈ S) :
      d ≤ 6 * C.card * restrictedHammingWeight A (column x j) :=
    escaping_column_restrictedWeight_ge_threshold h' x A d C
      hCard hSpanning hMin j (Finset.mem_inter.mp hj).1
  have hSumEach : d * S.card ≤
      (6 * C.card) * ∑ j ∈ S, restrictedHammingWeight A (column x j) := by
    calc
      d * S.card = ∑ _j ∈ S, d := by simp [mul_comm]
      _ ≤ ∑ j ∈ S, (6 * C.card) * restrictedHammingWeight A (column x j) :=
        Finset.sum_le_sum hEach
      _ = (6 * C.card) * ∑ j ∈ S, restrictedHammingWeight A (column x j) := by
        rw [Finset.mul_sum]
  have hSumSubset :
      (∑ j ∈ S, restrictedHammingWeight A (column x j)) ≤
      ∑ j ∈ B, restrictedHammingWeight A (column x j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    intros
    omega
  change d * S.card ≤ 6 * C.card * restrictedWeight x A B
  rw [restrictedWeight_eq_sum_column_restrictedHammingWeight]
  exact hSumEach.trans (Nat.mul_le_mul_left _ hSumSubset)
end QEC.Coding.ProductExpansion
