-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.row_correction_eq_zero_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:01:34.728945+00:00
-- url     : https://prove2.me/submissions/63a162c7-b28d-4aa3-89de-c30a9f5703d6

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_codeword_eq_zero_of_minimality_and_complement_bound
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
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d)
    (x correction : Matrix W W F)
    (hRows : ∀ i : W, row correction i ∈ (parityCheckCode h).carrier)
    (hCorrected : ∀ j ∈ A, column (x - correction) j = 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    correction = 0 := by
  ext i j
  have hZeroRow : row correction i = 0 := by
    apply codeword_eq_zero_of_minimality_and_complement_bound
      h d hDistance A delta hGap (row x i) (row correction i) (hRows i)
    · intro k hk
      have hentry := congrFun (hCorrected k hk) i
      simpa [row, column, Pi.sub_apply, Matrix.sub_apply] using hentry
    · have hNegative : -(row correction i) ∈ (parityCheckCode h).carrier :=
        (parityCheckCode h).carrier.neg_mem (hRows i)
      simpa [sub_eq_add_neg] using hMinimal.1 i (-(row correction i)) hNegative
  exact congrFun hZeroRow j
end QEC.Coding.ProductExpansion
