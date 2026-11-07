-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_columnsWithSyndromeInSpan_le_complement_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:10:12.852536+00:00
-- url     : https://prove2.me/submissions/99e9ed46-dbd3-45d8-a002-23ef5007b07d

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
import Theorems.Thm_QEC_Coding_ProductExpansion_generatorSupport_card_lt_one_third_of_small_restricted_weight
import Theorems.Thm_QEC_Coding_ProductExpansion_column_vanish_outside_generatorSupport_of_small_weight
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
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hWeight : (generatorRestrictedWeight A C : ℝ) < (d : ℝ) / 6) :
    (columnsWithSyndromeInSpan h' x C).card ≤ Fintype.card W - d := by
  classical
  let B := columnsWithSyndromeInSpan h' x C
  by_contra hNot
  have hLargeB : Fintype.card W - d < B.card := by
    change Fintype.card W - d < (columnsWithSyndromeInSpan h' x C).card
    omega
  have hRowsBound := card_nonzeroRowsOnColumns_ge_one_third_distance
    h h' d hPositive hLength hDistance hDistance'
      x hx hxNonzero hMinimal B hLargeB
  have hRowsSubset : nonzeroRowsOnColumns x B ⊆ generatorSupport C := by
    intro i hi
    obtain ⟨j, hjB, hxij⟩ : ∃ j ∈ B, x i j ≠ 0 := by
      simpa [nonzeroRowsOnColumns] using hi
    by_contra hiC
    have hjSpan : h'.mulVec (column x j) ∈ syndromeSpan h' C := by
      simpa [B, columnsWithSyndromeInSpan] using hjB
    have hZero := column_vanish_outside_generatorSupport_of_small_weight
      h h' d m hLength hSmallM hDistance' x hMinimal
      A hLargeA C hWeight j hjSpan i hiC
    exact hxij hZero
  have hRowsCard := Finset.card_le_card hRowsSubset
  have hSupportSmall := generatorSupport_card_lt_one_third_of_small_restricted_weight
    d m hLength hSmallM A hLargeA C hWeight
  have hRowsCardReal : ((nonzeroRowsOnColumns x B).card : ℝ) ≤
      (generatorSupport C).card := by exact_mod_cast hRowsCard
  linarith
end QEC.Coding.ProductExpansion
