-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_min_weight_generators_with_large_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:11:13.906837+00:00
-- url     : https://prove2.me/submissions/a87d5b3a-f1de-4d13-9c0c-b087acaded33

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_generatorSupport_card_ge_one_third_of_syndrome_spanning
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_min_weight_syndrome_generators

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
    (A : Finset W) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (d : ℝ) / 3 ≤ (generatorSupport C).card ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) ∧
      (∀ D : Finset (Word F W),
        D.card = (h' * x).rank →
        (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
        generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) := by
  obtain ⟨C, hCard, hSpanning, hMin⟩ :=
    exists_min_weight_syndrome_generators h' x A
  refine ⟨C, hCard, ?_, hSpanning, hMin⟩
  exact generatorSupport_card_ge_one_third_of_syndrome_spanning
    h h' d hPositive hLength hDistance hDistance'
    x hx hxNonzero hMinimal C hSpanning
end QEC.Coding.ProductExpansion
