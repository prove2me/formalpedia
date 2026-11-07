-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.cosetLeaderMatrix_mul_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:37:56.594847+00:00
-- url     : https://prove2.me/submissions/9cb991cb-59ea-4f3c-929e-c59f9e7812bd

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_cosetLeaderMatrix_isCosetLeader
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
omit [Fintype F] [DecidableEq W] [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i) :
    cosetLeaderMatrix h z x₀ hx₀ * h.transpose = z := by
  ext i r
  have hi := (cosetLeaderMatrix_isCosetLeader h z x₀ hx₀ i).1
  have hir := congrFun hi r
  simpa [Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct, row, mul_comm] using hir
end QEC.Coding.ProductExpansion
