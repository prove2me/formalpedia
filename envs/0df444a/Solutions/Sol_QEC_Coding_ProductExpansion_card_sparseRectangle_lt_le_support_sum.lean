-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_sparseRectangle_lt_le_support_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:02:12.69331+00:00
-- url     : https://prove2.me/submissions/6ecf5c24-d514-43cc-bc90-25e59b6c975f

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_sparseRectangleEncoding_injective
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
variable [Fintype W] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W] (A B : Finset W) (s : Nat) :
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
      ∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card) := by
  classical
  calc
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
        Nat.card (Σ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
          (((Finset.univ \ (A ×ˢ B) : Finset (W × W)) → F) × (S.1 → F))) :=
      Nat.card_le_card_of_injective
        (sparseRectangleEncoding (F := F) A B s)
        (sparseRectangleEncoding_injective (F := F) A B s)
    _ = ∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card) := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Nat.card_prod, Nat.card_fun, Nat.card_fun]
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe, pow_add]
end QEC.Coding.ProductExpansion
