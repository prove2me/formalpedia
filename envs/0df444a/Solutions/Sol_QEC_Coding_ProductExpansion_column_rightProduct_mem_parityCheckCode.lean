-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.column_rightProduct_mem_parityCheckCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:14.326205+00:00
-- url     : https://prove2.me/submissions/d7cb869d-8cbb-47bb-a8f1-a92a8fb5f645

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
    (x : Matrix W W F) (hx : ProductKernel h h' x) (j : R) :
    (fun i : W => (x * h.transpose) i j) ∈ (parityCheckCode h').carrier := by
  classical
  change (Matrix.toLin' h') (fun i : W => (x * h.transpose) i j) = 0
  ext i
  change h' * x * h.transpose = 0 at hx
  have hassoc : h' * (x * h.transpose) = 0 := by
    simpa only [Matrix.mul_assoc] using hx
  have hentry := congrArg (fun M : Matrix R' R F => M i j) hassoc
  simpa [Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply,
    dotProduct] using hentry
end QEC.Coding.ProductExpansion
