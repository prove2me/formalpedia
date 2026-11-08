-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.sq_add_one_pow_le_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:08:38.750221+00:00
-- url     : https://prove2.me/submissions/15f9f3db-63b3-44dd-a437-045eb27d8f4e

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
    (A : Nat) (hA : 0 < A) :
    (A ^ 2 + 1) ^ A ≤ 3 * A ^ (2 * A) := by
  have hOne : 1 ≤ A := hA
  have hBase : A ^ 2 + 1 ≤ A * (A + 1) := by
    nlinarith
  have hRatioReal :
      (((A + 1) ^ A : Nat) : ℝ) < 3 * (((A ^ A : Nat) : ℝ)) := by
    have hAReal : (0 : ℝ) < A := by exact_mod_cast hA
    calc
      (((A + 1) ^ A : Nat) : ℝ) =
          (A : ℝ) ^ A * (1 + (A : ℝ)⁻¹) ^ A := by
        push_cast
        rw [← mul_pow]
        congr 1
        field_simp
      _ ≤ (A : ℝ) ^ A * Real.exp 1 := by
        gcongr
        exact Real.one_add_inv_pow_le_exp
      _ < (A : ℝ) ^ A * 3 := by
        exact mul_lt_mul_of_pos_left Real.exp_one_lt_three (pow_pos hAReal _)
      _ = 3 * (((A ^ A : Nat) : ℝ)) := by
        push_cast
        ring
  have hRatio : (A + 1) ^ A ≤ 3 * A ^ A := by
    exact_mod_cast hRatioReal.le
  calc
    (A ^ 2 + 1) ^ A ≤ (A * (A + 1)) ^ A :=
      Nat.pow_le_pow_left hBase A
    _ = A ^ A * (A + 1) ^ A := by rw [mul_pow]
    _ ≤ A ^ A * (3 * A ^ A) := Nat.mul_le_mul_left _ hRatio
    _ = 3 * A ^ (2 * A) := by
      rw [show 2 * A = A + A by omega, pow_add]
      ring
end QEC.Coding.TannerLiftedProduct
