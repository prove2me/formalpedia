-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.support_set_card_ge_one_third_of_syndrome_lifts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:08:20.815384+00:00
-- url     : https://prove2.me/submissions/69715cee-4c60-49f8-892b-54dd3648f265

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_column_eq_small_support_syndrome_lift
import Theorems.Thm_QEC_Coding_ProductExpansion_card_nonzeroRows_ge_distance

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
    (S : Finset W)
    (hLifts : ∀ j : W, ∃ y : Word F W,
      (∀ i ∉ S, y i = 0) ∧ h'.mulVec y = h'.mulVec (column x j)) :
    (d : ℝ) / 3 ≤ S.card := by
  classical
  by_contra hNot
  have hSmall : (S.card : ℝ) < (d : ℝ) / 3 := lt_of_not_ge hNot
  have hAllColumnsSupported : ∀ j : W, ∀ i ∉ S, x i j = 0 := by
    intro j i hiS
    obtain ⟨y, hSupported, hSyndrome⟩ := hLifts j
    have hEqual := column_eq_small_support_syndrome_lift
      h h' d hDistance' x hMinimal S hSmall j y hSupported hSyndrome
    have hentry := congrFun hEqual i
    exact hentry.trans (hSupported i hiS)
  have hRowsSubset : nonzeroRows x ⊆ S := by
    intro i hi
    by_contra hiS
    have hRowNonzero := (Finset.mem_filter.mp hi).2
    apply hRowNonzero
    funext j
    exact hAllColumnsSupported j i hiS
  have hRowsCard := card_nonzeroRows_ge_distance h h' d
    hPositive hLength hDistance hDistance' x hx hxNonzero hMinimal
  have hSupportCard := Finset.card_le_card hRowsSubset
  have hRowsReal : (d : ℝ) ≤ (nonzeroRows x).card := by
    exact_mod_cast hRowsCard
  have hSupportReal : ((nonzeroRows x).card : ℝ) ≤ S.card := by
    exact_mod_cast hSupportCard
  linarith
end QEC.Coding.ProductExpansion
