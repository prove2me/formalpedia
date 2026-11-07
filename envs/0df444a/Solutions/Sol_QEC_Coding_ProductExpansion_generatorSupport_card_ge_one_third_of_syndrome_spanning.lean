-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.generatorSupport_card_ge_one_third_of_syndrome_spanning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:09:38.790022+00:00
-- url     : https://prove2.me/submissions/406948c8-f1af-48de-a17d-775f76402926

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_supported_syndrome_lift_of_mem_span
import Theorems.Thm_QEC_Coding_ProductExpansion_support_set_card_ge_one_third_of_syndrome_lifts

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
    (C : Finset (Word F W))
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    (d : ℝ) / 3 ≤ (generatorSupport C).card := by
  have hLifts : ∀ j : W, ∃ y : Word F W,
      (∀ i ∉ generatorSupport C, y i = 0) ∧
      h'.mulVec y = h'.mulVec (column x j) := by
    intro j
    exact exists_supported_syndrome_lift_of_mem_span
      h' C (h'.mulVec (column x j)) (hSpanning j)
  exact support_set_card_ge_one_third_of_syndrome_lifts
    h h' d hPositive hLength hDistance hDistance'
    x hx hxNonzero hMinimal (generatorSupport C) hLifts
end QEC.Coding.ProductExpansion
