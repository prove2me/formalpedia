-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_nonzeroColumnsOnRows_ge_one_third_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:37.735204+00:00
-- url     : https://prove2.me/submissions/dd02ad1d-f2a2-4104-b9ff-61d9b1d36c94

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
import Theorems.Thm_QEC_Coding_ProductExpansion_productKernel_transpose_iff
import Theorems.Thm_QEC_Coding_ProductExpansion_isDeltaMinimal_transpose_iff
import Theorems.Thm_QEC_Coding_ProductExpansion_card_nonzeroRowsOnColumns_ge_one_third_distance
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
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (B : Finset W) (hSizeB : Fintype.card W - d < B.card) :
    (d : ℝ) / 3 ≤ (nonzeroColumnsOnRows x B).card := by
  have hxT : ProductKernel h' h x.transpose :=
    (productKernel_transpose_iff h h' x).mp hx
  have hxTNonzero : x.transpose ≠ 0 := by
    intro hZero
    apply hxNonzero
    have hOriginal := congrArg Matrix.transpose hZero
    simpa using hOriginal
  have hMinimalT : IsDeltaMinimal h' h ((d : ℝ) / 3) x.transpose :=
    (isDeltaMinimal_transpose_iff h' h _ x).mpr hMinimal
  have hRows := card_nonzeroRowsOnColumns_ge_one_third_distance
    h' h d hPositive hLength hDistance' hDistance
    x.transpose hxT hxTNonzero hMinimalT B hSizeB
  have hTransposeRows :
      nonzeroRowsOnColumns x.transpose B = nonzeroColumnsOnRows x B := by
    classical
    unfold nonzeroRowsOnColumns nonzeroColumnsOnRows
    apply Finset.filter_congr
    intro i _
    simp only [Matrix.transpose_apply]
  rw [hTransposeRows] at hRows
  exact hRows
end QEC.Coding.ProductExpansion
