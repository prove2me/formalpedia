-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.local_syndrome_rank_ge_five_thirtysixths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:42.294196+00:00
-- url     : https://prove2.me/submissions/57d7d639-e0ce-47d7-acbe-3734c37ac180

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_local_syndrome_rank_weight_inequality_five_thirtysixths

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat) (s : ℝ)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A B : Finset W)
    (hLargeA : Fintype.card W - m ≤ A.card)
    (hLargeB : Fintype.card W - m ≤ B.card)
    (hSmallWeight : (restrictedWeight x A B : ℝ) < s)
    (hs : 0 < s) :
    (5 : ℝ) / 36 * (d : ℝ) ^ 2 / s ≤ ((h' * x).rank : ℝ) := by
  have hNat := local_syndrome_rank_weight_inequality_five_thirtysixths
    h h' d m hPositive hLength hSmallM hDistance hDistance'
      x hx hxNonzero hMinimal A B hLargeA hLargeB
  have hReal : (5 : ℝ) * d * d ≤
      36 * ((h' * x).rank : ℝ) * restrictedWeight x A B := by
    exact_mod_cast hNat
  have hRankNonneg : (0 : ℝ) ≤ ((h' * x).rank : ℝ) := Nat.cast_nonneg _
  have hProduct : ((h' * x).rank : ℝ) * restrictedWeight x A B ≤
      ((h' * x).rank : ℝ) * s :=
    mul_le_mul_of_nonneg_left hSmallWeight.le hRankNonneg
  rw [div_le_iff₀ hs]
  nlinarith [hProduct]
end QEC.Coding.ProductExpansion
