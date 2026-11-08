-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rootSchedule_coeff_realBudget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:33:04.512375+00:00
-- url     : https://prove2.me/submissions/0bbde5cd-1ed3-493a-8e34-74a3de6c4e36

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
    (A D M N x : Nat) (hA : 0 < A) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N)
    (hBudget : 12 * M + 6 ≤ D * x ^ 2) :
    4 * ((M * x ^ 4 : Nat) : ℝ) + 2 ≤
      ((D * N : Nat) : ℝ) /
          (3 * ((A * N : Nat) : ℝ)) *
        ((A * N : Nat) : ℝ) := by
  have hX4 : 0 < x ^ 4 := Nat.pow_pos hx
  have hNPositive : 0 < N := (Nat.pow_pos hx).trans_le hLower
  have hInteger : 12 * (M * x ^ 4) + 6 ≤ D * N := by
    calc
      12 * (M * x ^ 4) + 6 ≤ (12 * M + 6) * x ^ 4 := by
        nlinarith
      _ ≤ (D * x ^ 2) * x ^ 4 := Nat.mul_le_mul_right _ hBudget
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hLower
  have hReal :
      12 * ((M * x ^ 4 : Nat) : ℝ) + 6 ≤ (D * N : Nat) := by
    exact_mod_cast hInteger
  have hWNonzero : ((A * N : Nat) : ℝ) ≠ 0 := by
    positivity
  have hCancel :
      ((D * N : Nat) : ℝ) /
          (3 * ((A * N : Nat) : ℝ)) *
        ((A * N : Nat) : ℝ) =
      ((D * N : Nat) : ℝ) / 3 := by
    field_simp
  rw [hCancel]
  linarith
end QEC.Coding.TannerLiftedProduct
