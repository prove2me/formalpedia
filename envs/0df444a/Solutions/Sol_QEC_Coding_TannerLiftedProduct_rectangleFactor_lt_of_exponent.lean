-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rectangleFactor_lt_of_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:16:32.274247+00:00
-- url     : https://prove2.me/submissions/39e0be9f-579b-4eb7-86fb-5d4aa4b69849

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rectangleFactor_le_coarse
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleFactor_le_power

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
    (w m s q target : Nat) (hq : 2 ≤ q)
    (hExponent : coarseRectangleExponent w m s q + 3 < target) :
    6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ target := by
  have hqOne : 1 < q := by omega
  have hSix : 6 ≤ q ^ 3 := by
    calc
      6 ≤ 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hExact := rectangleFactor_le_coarse w m s q
  have hCoarse := coarseRectangleFactor_le_power w m s q hq
  calc
    6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
        (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
          q ^ (2 * (2 * m) * w + s))) ≤
        6 * coarseRectangleFactor w m s q :=
      Nat.mul_le_mul_left 6 hExact
    _ ≤ q ^ 3 * q ^ coarseRectangleExponent w m s q :=
      Nat.mul_le_mul hSix hCoarse
    _ = q ^ (coarseRectangleExponent w m s q + 3) := by
      rw [← pow_add, Nat.add_comm]
    _ < q ^ target := Nat.pow_lt_pow_right hqOne hExponent
end QEC.Coding.TannerLiftedProduct
