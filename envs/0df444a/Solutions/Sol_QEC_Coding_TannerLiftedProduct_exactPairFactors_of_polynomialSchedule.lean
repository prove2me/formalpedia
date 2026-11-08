-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exactPairFactors_of_polynomialSchedule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:33:37.297585+00:00
-- url     : https://prove2.me/submissions/9eb632a5-b11f-49cb-b686-f8a6c928061c

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactPairFactors_of_blocks
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_polynomial_lt_rank


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
    (A D B B' q L n : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 2 ≤ q) (hA : 0 < A) (hL : 0 < L) (hn : 0 < n)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D))
    (hForwardThreshold : 8 * A + 26 < B * n)
    (hReverseThreshold : 8 * A + 26 < B' * n) :
    (6 * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1) < q ^ (B * n ^ 6)) ∧
    (6 * (q ^ (B * n ^ 6) * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1)) < q ^ (A * n ^ 6)) ∧
    (6 * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1) < q ^ (B' * n ^ 6)) ∧
    (6 * (q ^ (B' * n ^ 6) * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1)) < q ^ (A * n ^ 6)) ∧
    (6 * ((Nat.choose (A * n ^ 6) (A * n ^ 6 - 2 * n ^ 4)) ^ 2 *
      (n ^ 7 * (((A * n ^ 6 - 2 * n ^ 4) *
        (A * n ^ 6 - 2 * n ^ 4) + 1) ^ (n ^ 7)) *
        q ^ (2 * (2 * n ^ 4) * (A * n ^ 6) + n ^ 7))) <
          q ^ (n ^ 5 * (B * n ^ 6))) ∧
    (6 * ((Nat.choose (A * n ^ 6) (A * n ^ 6 - 2 * n ^ 4)) ^ 2 *
      (n ^ 7 * (((A * n ^ 6 - 2 * n ^ 4) *
        (A * n ^ 6 - 2 * n ^ 4) + 1) ^ (n ^ 7)) *
        q ^ (2 * (2 * n ^ 4) * (A * n ^ 6) + n ^ 7))) <
          q ^ (n ^ 5 * (B' * n ^ 6))) := by
  apply exactPairFactors_of_blocks
    A D B B' (n ^ 4) (n ^ 7) (n ^ 5) q L (n ^ 6)
    hD hB hB' hq hL (Nat.pow_pos hn)
    hFirstKernelBlock hFirstImageBlock
    hSecondKernelBlock hSecondImageBlock
  · exact coarseRectangleExponent_polynomial_lt_rank
      A B n q hq hA hn hForwardThreshold
  · exact coarseRectangleExponent_polynomial_lt_rank
      A B' n q hq hA hn hReverseThreshold
end QEC.Coding.TannerLiftedProduct
