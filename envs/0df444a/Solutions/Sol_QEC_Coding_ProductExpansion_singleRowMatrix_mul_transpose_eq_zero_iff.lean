-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.singleRowMatrix_mul_transpose_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:41.284698+00:00
-- url     : https://prove2.me/submissions/39a998f7-5107-4879-82f3-9b4ec25da80f

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
omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (c : Word F W) :
    singleRowMatrix c * h.transpose = 0 ↔ h.mulVec c = 0 := by
  constructor
  · intro hZero
    funext r
    have hEntry := congrArg
      (fun M : Matrix (ULift.{v} Unit) R F => M (ULift.up ()) r) hZero
    simpa [singleRowMatrix, Matrix.mul_apply, Matrix.mulVec,
      Matrix.transpose_apply, dotProduct, mul_comm] using hEntry
  · intro hZero
    ext _ r
    have hEntry := congrFun hZero r
    simpa [singleRowMatrix, Matrix.mul_apply, Matrix.mulVec,
      Matrix.transpose_apply, dotProduct, mul_comm] using hEntry
end QEC.Coding.ProductExpansion
