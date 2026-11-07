-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.column_eq_small_support_syndrome_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:01:46.861268+00:00
-- url     : https://prove2.me/submissions/d8850cdb-a9ef-41e0-b851-d7bb9cde3ace

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_le_support_set_card
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_column_adjustment_eq_zero_of_small_residual
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
    (x : Matrix W W F)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (S : Finset W) (hSmall : (S.card : ℝ) < (d : ℝ) / 3)
    (j : W) (y : Word F W)
    (hSupport : ∀ i ∉ S, y i = 0)
    (hSyndrome : h'.mulVec y = h'.mulVec (column x j)) :
    column x j = y := by
  classical
  let c : Word F W := y - column x j
  have hc : c ∈ (parityCheckCode h').carrier := by
    change (Matrix.toLin' h') c = 0
    simp [Matrix.toLin'_apply, c, Matrix.mulVec_sub, hSyndrome]
  have hWeightNat := HammingWeight_le_support_set_card S y hSupport
  have hWeightReal : (HammingWeight y : ℝ) ≤ S.card := by
    exact_mod_cast hWeightNat
  have hAdjusted : column x j + c = y := by
    ext i
    simp [c]
  have hSmallAdjusted : (HammingWeight (column x j + c) : ℝ) <
      (d : ℝ) / 3 := by
    rw [hAdjusted]
    linarith
  have hZero := column_adjustment_eq_zero_of_small_residual
    h h' d hDistance' x hMinimal j c hc hSmallAdjusted
  have hEq : y - column x j = 0 := hZero
  exact (sub_eq_zero.mp hEq).symm
end QEC.Coding.ProductExpansion
