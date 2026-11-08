-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exactPairFactors_of_rootSchedule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:21:28.1133+00:00
-- url     : https://prove2.me/submissions/7a686473-48f2-44e2-9314-cc2455c9d7b2

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactPairFactors_of_blocks
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_rootSchedule_coeff_lt_rank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_25
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (A D M S K B B' q L N x : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 2 ≤ q) (hA : 0 < A) (hL : 0 < L) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D))
    (hForwardThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B * x)
    (hReverseThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B' * x) :
    (6 * (∑ t : Fin (D * N),
      Nat.choose (A * N) t.1 * q ^ t.1) < q ^ (B * N)) ∧
    (6 * (q ^ (B * N) * (∑ t : Fin (D * N),
      Nat.choose (A * N) t.1 * q ^ t.1)) < q ^ (A * N)) ∧
    (6 * (∑ t : Fin (D * N),
      Nat.choose (A * N) t.1 * q ^ t.1) < q ^ (B' * N)) ∧
    (6 * (q ^ (B' * N) * (∑ t : Fin (D * N),
      Nat.choose (A * N) t.1 * q ^ t.1)) < q ^ (A * N)) ∧
    (6 * ((Nat.choose (A * N) (A * N - 2 * (M * x ^ 4))) ^ 2 *
      (S * x ^ 7 * (((A * N - 2 * (M * x ^ 4)) *
        (A * N - 2 * (M * x ^ 4)) + 1) ^ (S * x ^ 7)) *
        q ^ (2 * (2 * (M * x ^ 4)) * (A * N) + S * x ^ 7))) <
          q ^ ((K * x ^ 5) * (B * N))) ∧
    (6 * ((Nat.choose (A * N) (A * N - 2 * (M * x ^ 4))) ^ 2 *
      (S * x ^ 7 * (((A * N - 2 * (M * x ^ 4)) *
        (A * N - 2 * (M * x ^ 4)) + 1) ^ (S * x ^ 7)) *
        q ^ (2 * (2 * (M * x ^ 4)) * (A * N) + S * x ^ 7))) <
          q ^ ((K * x ^ 5) * (B' * N))) := by
  apply exactPairFactors_of_blocks
    A D B B' (M * x ^ 4) (S * x ^ 7) (K * x ^ 5) q L N
    hD hB hB' hq hL ((Nat.pow_pos hx).trans_le hLower)
    hFirstKernelBlock hFirstImageBlock
    hSecondKernelBlock hSecondImageBlock
  · exact coarseRectangleExponent_rootSchedule_coeff_lt_rank
      A M S K B N x q hq hA hx hLower hUpper hForwardThreshold
  · exact coarseRectangleExponent_rootSchedule_coeff_lt_rank
      A M S K B' N x q hq hA hx hLower hUpper hReverseThreshold
end QEC.Coding.TannerLiftedProduct
