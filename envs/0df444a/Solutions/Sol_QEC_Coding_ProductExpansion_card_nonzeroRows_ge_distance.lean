-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_nonzeroRows_ge_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:06:11.617046+00:00
-- url     : https://prove2.me/submissions/238831a3-fb1a-41ce-adb3-71636c826fef

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
import Theorems.Thm_QEC_Coding_ProductExpansion_eq_zero_of_zero_rectangle_one_third
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
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x) :
    d ≤ (nonzeroRows x).card := by
  classical
  by_contra hNot
  have hFew : (nonzeroRows x).card < d := by omega
  let B : Finset W := Finset.univ \ nonzeroRows x
  have hBCard : B.card = Fintype.card W - (nonzeroRows x).card := by
    simpa [B] using Finset.card_sdiff_of_subset (Finset.subset_univ (nonzeroRows x))
  have hSizeB : Fintype.card W - d < B.card := by omega
  have hPositiveReal : (0 : ℝ) < d := by exact_mod_cast hPositive
  have hSizeA : (Fintype.card W : ℝ) - (Finset.univ : Finset W).card <
      (d : ℝ) / 3 := by simp; positivity
  have hRectangle :
      ∀ i ∈ B, ∀ j ∈ (Finset.univ : Finset W), x i j = 0 := by
    intro i hi j _
    have hZeroRow : row x i = 0 := by
      by_contra hRowNonzero
      have hiNonzero : i ∈ nonzeroRows x :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hRowNonzero⟩
      exact (Finset.mem_sdiff.mp hi).2 hiNonzero
    exact congrFun hZeroRow j
  have hZero := eq_zero_of_zero_rectangle_one_third h h' d
    hPositive hLength hDistance hDistance'
    Finset.univ B hSizeA hSizeB x hx hMinimal hRectangle
  exact hxNonzero hZero
end QEC.Coding.ProductExpansion
