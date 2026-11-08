-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exactPairFactors_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:18:55.813519+00:00
-- url     : https://prove2.me/submissions/221887e1-ecde-4669-873b-034df393850d

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactLowWeightFactors_of_blocks
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rectangleFactor_lt_of_exponent

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
    (A D B B' m s k q L n : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 2 ≤ q) (hL : 0 < L) (hn : 0 < n)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D))
    (hForwardRectangle :
      coarseRectangleExponent (A * n) m s q + 3 < k * (B * n))
    (hReverseRectangle :
      coarseRectangleExponent (A * n) m s q + 3 < k * (B' * n)) :
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B * n)) ∧
    (6 * (q ^ (B * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) ∧
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B' * n)) ∧
    (6 * (q ^ (B' * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) ∧
    (6 * ((Nat.choose (A * n) (A * n - 2 * m)) ^ 2 *
      (s * (((A * n - 2 * m) * (A * n - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * (A * n) + s))) < q ^ (k * (B * n))) ∧
    (6 * ((Nat.choose (A * n) (A * n - 2 * m)) ^ 2 *
      (s * (((A * n - 2 * m) * (A * n - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * (A * n) + s))) < q ^ (k * (B' * n))) := by
  obtain ⟨hFirstKernel, hFirstImage, hSecondKernel, hSecondImage⟩ :=
    exactLowWeightFactors_of_blocks A D B B' q L n
      hD hB hB' (by omega) hL hn hFirstKernelBlock hFirstImageBlock
      hSecondKernelBlock hSecondImageBlock
  exact ⟨hFirstKernel, hFirstImage, hSecondKernel, hSecondImage,
    rectangleFactor_lt_of_exponent
      (A * n) m s q (k * (B * n)) hq hForwardRectangle,
    rectangleFactor_lt_of_exponent
      (A * n) m s q (k * (B' * n)) hq hReverseRectangle⟩
end QEC.Coding.TannerLiftedProduct
