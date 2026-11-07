-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badChecksForRectangle_mul_rankPenalty_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:10:24.132135+00:00
-- url     : https://prove2.me/submissions/691e1010-b03a-45e1-8ca0-5af96945148a

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_productKernel_fixed_word_mul_field_pow_rankLower_le_total
import Theorems.Thm_QEC_Coding_ProductExpansion_badChecksForRectangleEncoding_injective
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
omit [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :
    Nat.card (badChecksForRectangle (R := R) h' A B s k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card {x : Matrix W W F // restrictedWeight x A B < s} *
        Nat.card (Matrix R W F) := by
  classical
  let X := {x : Matrix W W F //
    restrictedWeight x A B < s ∧ k ≤ (h' * x).rank}
  let E := Σ x : X, {g : Matrix R W F // ProductKernel g h' x.1}
  have hEncode : Nat.card (badChecksForRectangle (R := R) h' A B s k) ≤
      Nat.card E := Nat.card_le_card_of_injective
    (badChecksForRectangleEncoding (R := R) h' A B s k)
    (badChecksForRectangleEncoding_injective (R := R) h' A B s k)
  have hFiber (x : X) :
      Nat.card {g : Matrix R W F // ProductKernel g h' x.1} *
          (Nat.card F) ^ (k * Fintype.card R) ≤
        Nat.card (Matrix R W F) :=
    card_productKernel_fixed_word_mul_field_pow_rankLower_le_total
      h' x.1 k x.2.2
  have hSigma : Nat.card E * (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card X * Nat.card (Matrix R W F) := by
    rw [Nat.card_sigma, Finset.sum_mul]
    have hSum := Finset.sum_le_card_nsmul Finset.univ
      (fun x : X =>
        Nat.card {g : Matrix R W F // ProductKernel g h' x.1} *
          (Nat.card F) ^ (k * Fintype.card R))
      (Nat.card (Matrix R W F)) (fun x _ => hFiber x)
    simpa [nsmul_eq_mul, Nat.card_eq_fintype_card] using hSum
  have hX : Nat.card X ≤
      Nat.card {x : Matrix W W F // restrictedWeight x A B < s} :=
    Nat.card_le_card_of_injective
      (fun x : X => (⟨x.1, x.2.1⟩ :
        {x : Matrix W W F // restrictedWeight x A B < s}))
      (fun x y hxy => by
        apply Subtype.ext
        exact congrArg (fun z :
          {x : Matrix W W F // restrictedWeight x A B < s} => z.1) hxy)
  exact (Nat.mul_le_mul_right _ hEncode).trans <|
    hSigma.trans (Nat.mul_le_mul_right _ hX)
end QEC.Coding.ProductExpansion
