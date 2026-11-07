-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_nonzeroRowsOnColumns_ge_one_third_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:08:08.019492+00:00
-- url     : https://prove2.me/submissions/54ab32a0-325c-4957-af79-4ffb391e5748

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
import Theorems.Thm_QEC_Coding_ProductExpansion_eq_zero_of_zero_rectangle_one_third_either
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
    (d : ℝ) / 3 ≤ (nonzeroRowsOnColumns x B).card := by
  classical
  by_contra hNot
  have hFew : ((nonzeroRowsOnColumns x B).card : ℝ) < (d : ℝ) / 3 := by
    exact lt_of_not_ge hNot
  let S := nonzeroRowsOnColumns x B
  let A : Finset W := Finset.univ \ S
  have hSle : S.card ≤ Fintype.card W := Finset.card_le_univ S
  have hAcard : A.card = Fintype.card W - S.card := by
    simpa [A] using Finset.card_sdiff_of_subset (Finset.subset_univ S)
  have hCastComplement : (Fintype.card W : ℝ) - A.card = S.card := by
    rw [hAcard, Nat.cast_sub hSle]
    ring
  have hSizeA : (Fintype.card W : ℝ) - A.card < (d : ℝ) / 3 := by
    rw [hCastComplement]
    exact hFew
  have hRectangle : ∀ i ∈ A, ∀ j ∈ B, x i j = 0 := by
    intro i hi j hj
    by_contra hNonzero
    have hiS : i ∈ S := by
      simpa [S, nonzeroRowsOnColumns] using
        (show ∃ k ∈ B, x i k ≠ 0 from ⟨j, hj, hNonzero⟩)
    exact (Finset.mem_sdiff.mp hi).2 hiS
  have hZero := eq_zero_of_zero_rectangle_one_third_either h h' d
    hPositive hLength hDistance hDistance'
    A B hSizeA hSizeB x hx hMinimal (Or.inr hRectangle)
  exact hxNonzero hZero
end QEC.Coding.ProductExpansion
