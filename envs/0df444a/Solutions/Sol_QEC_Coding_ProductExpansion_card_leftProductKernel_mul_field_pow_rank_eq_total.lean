-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_leftProductKernel_mul_field_pow_rank_eq_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:54.886314+00:00
-- url     : https://prove2.me/submissions/8f6a489d-1b0e-44a5-993a-355f8d7e083c

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_leftProductKernel_eq_field_pow_nullity
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
    (M : Matrix R' W F) :
    Nat.card {h : Matrix R W F // M * h.transpose = 0} *
        (Nat.card F) ^ (M.rank * Fintype.card R) =
      Nat.card (Matrix R W F) := by
  classical
  have hTotal : Nat.card (Matrix R W F) =
      (Nat.card F) ^ (Fintype.card W * Fintype.card R) := by
    change Nat.card (R → W → F) = _
    rw [Nat.card_fun, Nat.card_fun]
    simp only [Nat.card_eq_fintype_card, pow_mul]
  rw [card_leftProductKernel_eq_field_pow_nullity, hTotal]
  have hRank : M.rank ≤ Fintype.card W := M.rank_le_card_width
  have hAdd : (Fintype.card W - M.rank) + M.rank = Fintype.card W :=
    Nat.sub_add_cancel hRank
  calc
    (Nat.card F) ^ ((Fintype.card W - M.rank) * Fintype.card R) *
        (Nat.card F) ^ (M.rank * Fintype.card R) =
      (Nat.card F) ^
        (((Fintype.card W - M.rank) + M.rank) * Fintype.card R) := by
          rw [add_mul, pow_add]
    _ = (Nat.card F) ^ (Fintype.card W * Fintype.card R) := by rw [hAdd]
end QEC.Coding.ProductExpansion
