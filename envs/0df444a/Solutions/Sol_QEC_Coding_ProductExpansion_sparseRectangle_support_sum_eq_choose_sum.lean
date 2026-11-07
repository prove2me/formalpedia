-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.sparseRectangle_support_sum_eq_choose_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:33.728577+00:00
-- url     : https://prove2.me/submissions/4f8af09e-1e09-4c67-9f0d-f9858ad7718b

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
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
omit [Field F] [DecidableEq F]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W] (A B : Finset W) (s : Nat) :
    (∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card)) =
      ∑ t : Fin s, Nat.choose (A.card * B.card) t.1 *
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + t.1) := by
  classical
  let U := A ×ˢ B
  let out := (Finset.univ \ U : Finset (W × W)).card
  let e := smallSubsetsEquivSigmaPowersetCard U s
  calc
    (∑ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + S.1.card)) =
      ∑ z : Σ t : Fin s, U.powersetCard t.1,
        (Nat.card F) ^ (out + z.1.1) := by
          apply Fintype.sum_equiv e
          intro S
          rfl
    _ = ∑ t : Fin s, Nat.choose U.card t.1 *
        (Nat.card F) ^ (out + t.1) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro t ht
          simp [Finset.card_powersetCard]
    _ = ∑ t : Fin s, Nat.choose (A.card * B.card) t.1 *
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + t.1) := by
          simp only [U, out, Finset.card_product]
end QEC.Coding.ProductExpansion
