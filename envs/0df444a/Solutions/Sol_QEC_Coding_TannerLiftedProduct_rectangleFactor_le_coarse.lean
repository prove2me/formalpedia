-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rectangleFactor_le_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:13:09.626298+00:00
-- url     : https://prove2.me/submissions/d4f78ffa-cbab-4d4b-9f65-d77cf6b0bb0e

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair

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
    (w m s q : Nat) :
    (Nat.choose w (w - 2 * m)) ^ 2 *
        (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
          q ^ (2 * (2 * m) * w + s)) ≤
      coarseRectangleFactor w m s q := by
  have hChoose : Nat.choose w (w - 2 * m) ≤ 2 ^ w :=
    Nat.choose_le_two_pow w (w - 2 * m)
  have hChooseSq : (Nat.choose w (w - 2 * m)) ^ 2 ≤ 4 ^ w := by
    calc
      (Nat.choose w (w - 2 * m)) ^ 2 ≤ (2 ^ w) ^ 2 :=
        Nat.pow_le_pow_left hChoose 2
      _ = 4 ^ w := by
        rw [← pow_mul, Nat.mul_comm w 2, pow_mul]
        norm_num
  have hSide :
      (w - 2 * m) * (w - 2 * m) + 1 ≤ w * w + 1 := by
    gcongr <;> omega
  unfold coarseRectangleFactor
  have hExponent : 2 * (2 * m) * w + s = 4 * m * w + s := by ring
  have hMiddle :
      s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
          q ^ (2 * (2 * m) * w + s) ≤
        s * ((w * w + 1) ^ s) * q ^ (4 * m * w + s) := by
    rw [hExponent]
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left s (Nat.pow_le_pow_left hSide s))
  exact Nat.mul_le_mul hChooseSq hMiddle
end QEC.Coding.TannerLiftedProduct
