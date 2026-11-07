-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.leftProduct_sub_mapRows_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:56:51.012265+00:00
-- url     : https://prove2.me/submissions/b617df92-8abf-4c59-8d84-5b8012f497fd

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_row_leftProduct_mem_parityCheckCode
import Theorems.Thm_QEC_Coding_ProductExpansion_mapRows_left_mul
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
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (T : Word F W →ₗ[F] Word F W)
    (hFix : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier → T c = c) :
    h' * (x - mapRows T x) = 0 := by
  have hRows : mapRows T (h' * x) = h' * x := by
    ext i j
    exact congrFun (hFix ((h' * x) i)
      (row_leftProduct_mem_parityCheckCode h h' x hx i)) j
  calc
    h' * (x - mapRows T x) = h' * x - h' * mapRows T x := by
      rw [Matrix.mul_sub]
    _ = h' * x - mapRows T (h' * x) := by
      rw [mapRows_left_mul]
    _ = 0 := by rw [hRows]; simp
end QEC.Coding.ProductExpansion
