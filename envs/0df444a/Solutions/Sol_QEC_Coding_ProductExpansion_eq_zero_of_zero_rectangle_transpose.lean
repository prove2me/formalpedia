-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.eq_zero_of_zero_rectangle_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:31.12637+00:00
-- url     : https://prove2.me/submissions/50fb24a4-189a-411e-8ff2-a13d15a3685e

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_eq_zero_of_zero_rectangle
import Theorems.Thm_QEC_Coding_ProductExpansion_productKernel_transpose_iff
import Theorems.Thm_QEC_Coding_ProductExpansion_isDeltaMinimal_transpose_iff
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d d' : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d' ≤ HammingWeight c)
    (A B : Finset W)
    (hLargeA : Fintype.card W - d' < A.card)
    (hLargeB : Fintype.card W - d < B.card)
    (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d')
    (hDelta : delta < d)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hMinimal : IsDeltaMinimal h h' delta x)
    (hRectangle : ∀ i ∈ A, ∀ j ∈ B, x i j = 0) :
    x = 0 := by
  have hTransposeKernel : ProductKernel h' h x.transpose :=
    (productKernel_transpose_iff h h' x).mp hx
  have hTransposeMinimal : IsDeltaMinimal h' h delta x.transpose :=
    (isDeltaMinimal_transpose_iff h' h delta x).mpr hMinimal
  have hTransposeRectangle :
      ∀ i ∈ B, ∀ j ∈ A, x.transpose i j = 0 := by
    intro i hi j hj
    exact hRectangle j hj i hi
  have hTransposeZero :=
    eq_zero_of_zero_rectangle h' h d' d hDistance' hDistance
      A B hLargeA hLargeB delta hGap hDelta
      x.transpose hTransposeKernel hTransposeMinimal hTransposeRectangle
  have hOriginal := congrArg Matrix.transpose hTransposeZero
  simpa using hOriginal
end QEC.Coding.ProductExpansion
