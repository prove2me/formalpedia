-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.polynomialSchedule_coeff_realBudget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:33:01.7472+00:00
-- url     : https://prove2.me/submissions/df311cf1-f900-4ca4-9b9b-f85f62d5393d

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
    (A D M n : Nat) (hA : 0 < A) (hn : 0 < n)
    (hBudget : 12 * M + 6 ≤ D * n ^ 2) :
    4 * ((M * n ^ 4 : Nat) : ℝ) + 2 ≤
      ((D * n ^ 6 : Nat) : ℝ) /
          (3 * ((A * n ^ 6 : Nat) : ℝ)) *
        ((A * n ^ 6 : Nat) : ℝ) := by
  have hN4 : 0 < n ^ 4 := Nat.pow_pos hn
  have hInteger : 12 * (M * n ^ 4) + 6 ≤ D * n ^ 6 := by
    calc
      12 * (M * n ^ 4) + 6 ≤ (12 * M + 6) * n ^ 4 := by
        nlinarith
      _ ≤ (D * n ^ 2) * n ^ 4 := Nat.mul_le_mul_right _ hBudget
      _ = D * n ^ 6 := by ring
  have hReal :
      12 * ((M * n ^ 4 : Nat) : ℝ) + 6 ≤ (D * n ^ 6 : Nat) := by
    exact_mod_cast hInteger
  have hWNonzero : ((A * n ^ 6 : Nat) : ℝ) ≠ 0 := by
    positivity
  have hCancel :
      ((D * n ^ 6 : Nat) : ℝ) /
          (3 * ((A * n ^ 6 : Nat) : ℝ)) *
        ((A * n ^ 6 : Nat) : ℝ) =
      ((D * n ^ 6 : Nat) : ℝ) / 3 := by
    field_simp
  rw [hCancel]
  linarith
end QEC.Coding.TannerLiftedProduct
