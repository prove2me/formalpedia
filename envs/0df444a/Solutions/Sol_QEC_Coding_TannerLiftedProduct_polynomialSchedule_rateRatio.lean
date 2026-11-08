-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.polynomialSchedule_rateRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:33:09.633173+00:00
-- url     : https://prove2.me/submissions/0ad796e4-6bb0-4643-aeb6-9e04f4193d71

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds

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
    (A B B' n : Nat) (rate : ℝ)
    (hCoefficient :
      2 * ((B : ℝ) + B') * A ≤
        (1 - rate) * ((A : ℝ) ^ 2 + 4 * B * B')) :
    2 * (((B * n ^ 6 : Nat) : ℝ) + (B' * n ^ 6 : Nat)) *
        ((A * n ^ 6 : Nat) : ℝ) ≤
      (1 - rate) *
        (((A * n ^ 6 : Nat) : ℝ) ^ 2 +
          4 * ((B * n ^ 6 : Nat) : ℝ) * (B' * n ^ 6 : Nat)) := by
  have hScale : 0 ≤ (((n ^ 6 : Nat) : ℝ) ^ 2) := sq_nonneg _
  have hScaled := mul_le_mul_of_nonneg_right hCoefficient hScale
  norm_num only [Nat.cast_mul, Nat.cast_pow] at ⊢ hScaled
  nlinarith
end QEC.Coding.TannerLiftedProduct
