-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_min_weight_generators_with_one_sixth_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:48.253446+00:00
-- url     : https://prove2.me/submissions/d9e98a24-2681-4fc2-889a-0bdfa33ce8b2

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_generatorRestrictedWeight_ge_one_sixth_of_large_support
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_min_weight_generators_with_large_support

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
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (d : ℝ) / 6 ≤ generatorRestrictedWeight A C ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) ∧
      (∀ D : Finset (Word F W),
        D.card = (h' * x).rank →
        (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
        generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) := by
  obtain ⟨C, hCard, hSupport, hSpanning, hMin⟩ :=
    exists_min_weight_generators_with_large_support
      h h' d hPositive hLength hDistance hDistance'
      x hx hxNonzero hMinimal A
  refine ⟨C, hCard, ?_, hSpanning, hMin⟩
  exact generatorRestrictedWeight_ge_one_sixth_of_large_support
    d m hLength hSmallM A hLargeA C hSupport
end QEC.Coding.ProductExpansion
