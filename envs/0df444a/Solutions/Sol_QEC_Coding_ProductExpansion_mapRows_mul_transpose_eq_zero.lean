-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.mapRows_mul_transpose_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:21.835528+00:00
-- url     : https://prove2.me/submissions/ef9cc3cc-e8c4-4a32-94ef-7443bab2fd85

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
    (h : Matrix R W F) (T : Word F W →ₗ[F] Word F W)
    (hImage : ∀ y : Word F W, T y ∈ (parityCheckCode h).carrier)
    (x : Matrix W W F) :
    mapRows T x * h.transpose = 0 := by
  classical
  ext i j
  have hm := hImage (x i)
  change (Matrix.toLin' h) (T (x i)) = 0 at hm
  have hentry := congrFun hm j
  simpa [mapRows, Matrix.toLin'_apply, Matrix.mulVec,
    Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mul_comm] using hentry
end QEC.Coding.ProductExpansion
