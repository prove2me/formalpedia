-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.local_syndrome_rank_weight_inequality_five_thirtysixths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:18:05.747823+00:00
-- url     : https://prove2.me/submissions/2167d91f-3545-4d3e-afe6-1f0dca45f01f

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_local_syndrome_rank_weight_inequality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
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
    (A B : Finset W)
    (hLargeA : Fintype.card W - m ≤ A.card)
    (hLargeB : Fintype.card W - m ≤ B.card) :
    5 * d * d ≤ 36 * (h' * x).rank * restrictedWeight x A B := by
  have hBase := local_syndrome_rank_weight_inequality
    h h' d m hPositive hLength hSmallM hDistance hDistance'
      x hx hxNonzero hMinimal A B hLargeA hLargeB
  have hmLe : m ≤ d := by omega
  have hSub : d - m + m = d := Nat.sub_add_cancel hmLe
  have hDistanceTimes := Nat.mul_le_mul_left d hSmallM
  have hBaseTimes := Nat.mul_le_mul_left 6 hBase
  nlinarith
end QEC.Coding.ProductExpansion
