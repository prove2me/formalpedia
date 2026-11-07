-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.lightGenerators_restrictedWeight_lt_one_sixth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:57:19.084525+00:00
-- url     : https://prove2.me/submissions/ab9ddf42-3fa2-4e3b-9325-a96498c2b7ef

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
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (A : Finset W) (C : Finset (Word F W)) (d : Nat)
    (hCPositive : 0 < C.card) (hDPositive : 0 < d) :
    (generatorRestrictedWeight A (lightGenerators A C d) : ℝ) < (d : ℝ) / 6 := by
  classical
  let T := lightGenerators A C d
  have hTSubset : T ⊆ C := by
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  have hTCard : (T.card : ℝ) ≤ C.card := by
    exact_mod_cast Finset.card_le_card hTSubset
  have hCPositiveReal : (0 : ℝ) < C.card := by exact_mod_cast hCPositive
  have hDPositiveReal : (0 : ℝ) < d := by exact_mod_cast hDPositive
  by_cases hTEmpty : T = ∅
  · simp [T, hTEmpty, generatorRestrictedWeight]
    positivity
  · have hTNonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTEmpty
    have hEach (y : Word F W) (hy : y ∈ T) :
        (6 : ℝ) * C.card * restrictedHammingWeight A y < d := by
      have hNat : 6 * C.card * restrictedHammingWeight A y < d :=
        (Finset.mem_filter.mp hy).2
      exact_mod_cast hNat
    have hSum := Finset.sum_lt_sum_of_nonempty hTNonempty hEach
    have hSumLt : (6 : ℝ) * C.card * generatorRestrictedWeight A T <
        (T.card : ℝ) * d := by
      simpa [generatorRestrictedWeight, Finset.mul_sum,
        Nat.cast_sum, Nat.cast_mul] using hSum
    have hCardTimes : (T.card : ℝ) * d ≤ C.card * d :=
      mul_le_mul_of_nonneg_right hTCard hDPositiveReal.le
    have hBound : (C.card : ℝ) *
        ((6 : ℝ) * generatorRestrictedWeight A T) < C.card * d := by
      nlinarith
    have hSmall : (6 : ℝ) * generatorRestrictedWeight A T < d :=
      (mul_lt_mul_iff_of_pos_left hCPositiveReal).mp hBound
    linarith
end QEC.Coding.ProductExpansion
