-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.restrictedWeight_ge_of_many_heavy_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:40.786574+00:00
-- url     : https://prove2.me/submissions/06604c25-076d-4463-be56-a3880894f183

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_eq_sum_row_restrictedHammingWeight
import Theorems.Thm_QEC_Coding_ProductExpansion_distance_le_four_mul_restrictedHammingWeight
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
    (f : Matrix W W F) (A B J₂ : Finset W) (d m s : Nat)
    (hJ₂B : J₂ ⊆ B)
    (hA : Fintype.card W - m ≤ A.card)
    (hCount : m < J₂.card)
    (hHeavy : ∀ i ∈ J₂, d ≤ 2 * HammingWeight (row f i))
    (hDistance : 4 * m ≤ d)
    (hScale : 4 * s ≤ m * d) :
    s ≤ restrictedWeight f B A := by
  have hEach : ∀ i ∈ J₂,
      d ≤ 4 * restrictedHammingWeight A (row f i) := by
    intro i hi
    exact distance_le_four_mul_restrictedHammingWeight
      A (row f i) d m hA (hHeavy i hi) hDistance
  have hSum : J₂.card * d ≤
      4 * ∑ i ∈ J₂, restrictedHammingWeight A (row f i) := by
    calc
      J₂.card * d = ∑ _i ∈ J₂, d := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ J₂, 4 * restrictedHammingWeight A (row f i) := by
        exact Finset.sum_le_sum fun i hi => hEach i hi
      _ = 4 * ∑ i ∈ J₂, restrictedHammingWeight A (row f i) := by
        rw [Finset.mul_sum]
  have hRestricted :
      ∑ i ∈ J₂, restrictedHammingWeight A (row f i) ≤
        restrictedWeight f B A := by
    rw [restrictedWeight_eq_sum_row_restrictedHammingWeight]
    exact Finset.sum_le_sum_of_subset_of_nonneg hJ₂B (by simp)
  have hCountMul : m * d ≤ J₂.card * d :=
    Nat.mul_le_mul_right d (Nat.le_of_lt hCount)
  have hFour : 4 * s ≤ 4 * restrictedWeight f B A :=
    hScale.trans <| hCountMul.trans <|
      hSum.trans (Nat.mul_le_mul_left 4 hRestricted)
  omega
end QEC.Coding.ProductExpansion
