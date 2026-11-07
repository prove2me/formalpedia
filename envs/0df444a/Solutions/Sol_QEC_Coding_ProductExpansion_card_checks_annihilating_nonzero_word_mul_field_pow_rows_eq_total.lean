-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:48.344833+00:00
-- url     : https://prove2.me/submissions/2f5dd7e1-2d94-4168-96f8-ed913115e28c

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_rank_singleRowMatrix_eq_one
import Theorems.Thm_QEC_Coding_ProductExpansion_singleRowMatrix_mul_transpose_eq_zero_iff
import Theorems.Thm_QEC_Coding_ProductExpansion_card_leftProductKernel_mul_field_pow_rank_eq_total
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
omit [DecidableEq F] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (c : Word F W) (hc : c ≠ 0) :
    Nat.card {h : Matrix R W F // h.mulVec c = 0} *
        (Nat.card F) ^ Fintype.card R = Nat.card (Matrix R W F) := by
  let e : {h : Matrix R W F // h.mulVec c = 0} ≃
      {h : Matrix R W F // singleRowMatrix c * h.transpose = 0} :=
    Equiv.subtypeEquivRight (fun h =>
      (singleRowMatrix_mul_transpose_eq_zero_iff h c).symm)
  rw [Nat.card_congr e]
  simpa [rank_singleRowMatrix_eq_one c hc, one_mul] using
    card_leftProductKernel_mul_field_pow_rank_eq_total
      (R := R) (singleRowMatrix c)
end QEC.Coding.ProductExpansion
