-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.productExpanding_of_no_ranked_sparse_exactRectangle_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:21:36.135199+00:00
-- url     : https://prove2.me/submissions/c71f35f3-bd89-4503-92a3-bbb8b3e93a08

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_badChecksAllExactRectangles_of_local_failure

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d m s k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hNoBad : ¬∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (h' * x).rank ∧ ProductKernel h h' x) :
    ProductExpanding h h' s m
      ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  have hwPositiveNat : 0 < Fintype.card W := hPositive.trans_le hLength
  have hwPositive : (0 : ℝ) < Fintype.card W := by exact_mod_cast hwPositiveNat
  have hBeta :
      ((d : ℝ) / (3 * (Fintype.card W : ℝ))) * Fintype.card W =
        (d : ℝ) / 3 := by
    field_simp
  intro x hx hxNonzero hMinimal A B hLargeA hLargeB
  rw [hBeta] at hMinimal
  by_contra hNotWeight
  have hWeight : restrictedWeight x A B < s := Nat.lt_of_not_ge hNotWeight
  obtain ⟨bad, hbad⟩ := exists_badChecksAllExactRectangles_of_local_failure
    h h' d m s k hPositive hLength hSmallM hRankTarget
      hDistance hDistance' x hx hxNonzero hMinimal A B hLargeA hLargeB hWeight
  subst hbad
  exact hNoBad bad.2
end QEC.Coding.ProductExpansion
