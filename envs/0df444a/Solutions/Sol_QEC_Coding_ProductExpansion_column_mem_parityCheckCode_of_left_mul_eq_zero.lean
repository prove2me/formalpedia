-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.column_mem_parityCheckCode_of_left_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:29:38.880928+00:00
-- url     : https://prove2.me/submissions/76ccf15e-b5ce-4df4-8ea8-c5a0e05b85ae

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
omit [DecidableEq F] [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (x : Matrix W W F) (hx : h * x = 0) (j : W) :
    column x j ∈ (parityCheckCode h).carrier := by
  classical
  change (Matrix.toLin' h) (fun i : W => x i j) = 0
  ext i
  have hentry := congrArg (fun M : Matrix R W F => M i j) hx
  simpa [Matrix.toLin'_apply, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, column] using hentry
end QEC.Coding.ProductExpansion
