-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.row_leftProduct_mem_parityCheckCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:54:55.783547+00:00
-- url     : https://prove2.me/submissions/30e5644b-4317-4c18-8212-d2f8e0e42fd2

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [DecidableEq F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) (hx : ProductKernel h h' x) (i : R') :
    (h' * x) i ∈ (parityCheckCode h).carrier := by
  classical
  change (Matrix.toLin' h) ((h' * x) i) = 0
  ext j
  have hentry := congrArg (fun M : Matrix R' R F => M i j) hx
  simp only [Matrix.zero_apply] at hentry
  simpa [Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply,
    Matrix.transpose_apply, dotProduct, mul_comm] using hentry
end QEC.Coding.ProductExpansion
