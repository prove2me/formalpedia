-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_rootSchedule_coeff_lt_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:32:32.49276+00:00
-- url     : https://prove2.me/submissions/64f1fc08-8f11-45d7-9809-b4e722cebb9c

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_mono_width
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_polynomial_coeff_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (A M S K B N x q : Nat)
    (hq : 2 ≤ q) (hA : 0 < A) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B * x) :
    coarseRectangleExponent (A * N) (M * x ^ 4) (S * x ^ 7) q + 3 <
      (K * x ^ 5) * (B * N) := by
  have hWidth : A * N ≤ (64 * A) * x ^ 6 := by
    calc
      A * N ≤ A * (64 * x ^ 6) := Nat.mul_le_mul_left A hUpper
      _ = (64 * A) * x ^ 6 := by ring
  have hCoarse :
      coarseRectangleExponent (A * N) (M * x ^ 4) (S * x ^ 7) q + 3 ≤
        (2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11) * x ^ 10 := by
    calc
      coarseRectangleExponent (A * N) (M * x ^ 4) (S * x ^ 7) q + 3 ≤
          coarseRectangleExponent
              ((64 * A) * x ^ 6) (M * x ^ 4) (S * x ^ 7) q + 3 := by
        exact Nat.add_le_add_right
          (coarseRectangleExponent_mono_width
            (A * N) ((64 * A) * x ^ 6) (M * x ^ 4) (S * x ^ 7) q hWidth) 3
      _ ≤ (2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11) * x ^ 10 :=
        coarseRectangleExponent_polynomial_coeff_le
          (64 * A) M S x q hq (Nat.mul_pos (by norm_num) hA) hx
  have hStrict :
      (2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11) * x ^ 10 <
        (K * B * x) * x ^ 10 :=
    (Nat.mul_lt_mul_right (Nat.pow_pos hx)).2 hThreshold
  calc
    coarseRectangleExponent (A * N) (M * x ^ 4) (S * x ^ 7) q + 3 <
        (K * B * x) * x ^ 10 := hCoarse.trans_lt hStrict
    _ = (K * x ^ 5) * (B * x ^ 6) := by ring
    _ ≤ (K * x ^ 5) * (B * N) := by gcongr
end QEC.Coding.TannerLiftedProduct
