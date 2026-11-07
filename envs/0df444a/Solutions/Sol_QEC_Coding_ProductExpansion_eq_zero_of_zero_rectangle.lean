-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.eq_zero_of_zero_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:00.800008+00:00
-- url     : https://prove2.me/submissions/83699504-e149-43b9-9936-5a6137954209

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_row_correction_of_zero_rectangle
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_eq_zero_of_left_mul_eq_zero_and_minimal
import Theorems.Thm_QEC_Coding_ProductExpansion_row_correction_eq_zero_of_gap
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
    (hLargeA : Fintype.card W - d < A.card)
    (hLargeB : Fintype.card W - d' < B.card)
    (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d)
    (hDelta : delta < d')
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hMinimal : IsDeltaMinimal h h' delta x)
    (hRectangle : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    x = 0 := by
  obtain ⟨correction, hLeft, hColumns, hRows⟩ :=
    exists_row_correction_of_zero_rectangle h h' d d'
      hDistance hDistance' A B hLargeA hLargeB x hx hRectangle
  have hCorrectionZero : correction = 0 :=
    row_correction_eq_zero_of_gap h h' d hDistance A delta hGap
      x correction hRows hColumns hMinimal
  have hLeftZero : h' * x = 0 := by
    simpa [hCorrectionZero] using hLeft
  exact eq_zero_of_left_mul_eq_zero_and_minimal
    h h' d' hDistance' delta hDelta x hLeftZero hMinimal
end QEC.Coding.ProductExpansion
