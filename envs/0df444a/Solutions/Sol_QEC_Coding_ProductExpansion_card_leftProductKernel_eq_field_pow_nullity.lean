-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_leftProductKernel_eq_field_pow_nullity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:02:16.776646+00:00
-- url     : https://prove2.me/submissions/c01e6171-a6f7-4bdd-9d4f-7bc43ac723e3

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_leftProductKernel_eq_card_kernel_pow
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
    Nat.card {h : Matrix R W F // M * h.transpose = 0} =
      (Nat.card F) ^ ((Fintype.card W - M.rank) * Fintype.card R) := by
  classical
  have hRankNullity := (M.mulVecLin).finrank_range_add_finrank_ker
  have hKer : Module.finrank F (LinearMap.ker M.mulVecLin) =
      Fintype.card W - M.rank := by
    have hRank : Module.finrank F (LinearMap.range M.mulVecLin) = M.rank := rfl
    have hDomain : Module.finrank F (W → F) = Fintype.card W := by simp
    omega
  rw [card_leftProductKernel_eq_card_kernel_pow]
  rw [Module.natCard_eq_pow_finrank (K := F)
    (V := LinearMap.ker M.mulVecLin), hKer]
  simp only [Nat.card_eq_fintype_card, pow_mul]
end QEC.Coding.ProductExpansion
