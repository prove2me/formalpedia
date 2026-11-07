-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.eq_zero_of_left_mul_eq_zero_and_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:31:52.852625+00:00
-- url     : https://prove2.me/submissions/a39f30f7-08be-4549-9d24-245d659da780

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_column_mem_parityCheckCode_of_left_mul_eq_zero
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
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
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (hDelta : delta < d)
    (x : Matrix W W F) (hLeft : h' * x = 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    x = 0 := by
  ext i j
  have hColumn : column x j ∈ (parityCheckCode h').carrier :=
    column_mem_parityCheckCode_of_left_mul_eq_zero h' x hLeft j
  have hColumnZero : column x j = 0 := by
    by_contra hNonzero
    have hDistanceNat := hDistance' (column x j) hColumn hNonzero
    have hNegative : -(column x j) ∈ (parityCheckCode h').carrier :=
      (parityCheckCode h').carrier.neg_mem hColumn
    have hMinimalColumn := hMinimal.2 j (-(column x j)) hNegative
    have hWeight : (HammingWeight (column x j) : ℝ) ≤ delta := by
      simpa using hMinimalColumn
    have hDistanceReal : (d : ℝ) ≤ HammingWeight (column x j) := by
      exact_mod_cast hDistanceNat
    linarith
  exact congrFun hColumnZero i
end QEC.Coding.ProductExpansion
