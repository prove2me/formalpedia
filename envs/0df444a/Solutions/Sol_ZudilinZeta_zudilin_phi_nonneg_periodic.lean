-- Prove2me | solution 1 for ZudilinZeta.zudilin_phi_nonneg_periodic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:06:44.397389+00:00
-- url     : https://prove2.me/submissions/c74c01b0-dbc0-4054-acf6-232df78455ed

import Definitions.Def_ZudilinZetaArith

open ZudilinZeta

namespace Ag4Aux_ZudPhi

theorem t1_nonneg (e0 ej x y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ ⌊y⌋ + ⌊e0 * x - y⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ - 2 * ⌊ej * x⌋ := by
  have hy : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hy0, hy1⟩
  have h1 : ⌊(e0 - ej) * x - y⌋ + ⌊ej * x⌋ ≤ ⌊e0 * x - y⌋ := by
    rw [Int.le_floor]; push_cast
    linarith [Int.floor_le ((e0 - ej) * x - y), Int.floor_le (ej * x)]
  have h2 : ⌊ej * x⌋ + ⌊y - ej * x⌋ ≤ ⌊y⌋ := by
    rw [Int.le_floor]; push_cast
    linarith [Int.floor_le (y - ej * x), Int.floor_le (ej * x)]
  omega

theorem t2_nonneg (e0 ej x y : ℝ) :
    0 ≤ ⌊(e0 - 2 * ej) * x⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ := by
  have h : ⌊y - ej * x⌋ + ⌊(e0 - ej) * x - y⌋ ≤ ⌊(e0 - 2 * ej) * x⌋ := by
    rw [Int.le_floor]; push_cast
    linarith [Int.floor_le (y - ej * x), Int.floor_le ((e0 - ej) * x - y)]
  omega

theorem t1_per (e0 ej : ℕ) (x y : ℝ) :
    ⌊y⌋ + ⌊(e0 : ℝ) * (x + 1) - y⌋ - ⌊y - (ej : ℝ) * (x + 1)⌋
        - ⌊((e0 : ℝ) - (ej : ℝ)) * (x + 1) - y⌋ - 2 * ⌊(ej : ℝ) * (x + 1)⌋
      = ⌊y⌋ + ⌊(e0 : ℝ) * x - y⌋ - ⌊y - (ej : ℝ) * x⌋
        - ⌊((e0 : ℝ) - (ej : ℝ)) * x - y⌋ - 2 * ⌊(ej : ℝ) * x⌋ := by
  have a1 : ⌊(e0 : ℝ) * (x + 1) - y⌋ = ⌊(e0 : ℝ) * x - y⌋ + e0 := by
    rw [show (e0 : ℝ) * (x + 1) - y = ((e0 : ℝ) * x - y) + (e0 : ℕ) by ring,
      Int.floor_add_natCast]
  have a2 : ⌊y - (ej : ℝ) * (x + 1)⌋ = ⌊y - (ej : ℝ) * x⌋ - ej := by
    rw [show y - (ej : ℝ) * (x + 1) = (y - (ej : ℝ) * x) - (ej : ℕ) by ring,
      Int.floor_sub_natCast]
  have a3 : ⌊((e0 : ℝ) - (ej : ℝ)) * (x + 1) - y⌋
      = ⌊((e0 : ℝ) - (ej : ℝ)) * x - y⌋ + ((e0 : ℤ) - (ej : ℤ)) := by
    rw [show ((e0 : ℝ) - (ej : ℝ)) * (x + 1) - y
        = (((e0 : ℝ) - (ej : ℝ)) * x - y) + (((e0 : ℤ) - (ej : ℤ) : ℤ) : ℝ) by push_cast; ring,
      Int.floor_add_intCast]
  have a4 : ⌊(ej : ℝ) * (x + 1)⌋ = ⌊(ej : ℝ) * x⌋ + ej := by
    rw [show (ej : ℝ) * (x + 1) = ((ej : ℝ) * x) + (ej : ℕ) by ring, Int.floor_add_natCast]
  rw [a1, a2, a3, a4]; ring

theorem t2_per (e0 ej : ℕ) (x y : ℝ) :
    ⌊((e0 : ℝ) - 2 * (ej : ℝ)) * (x + 1)⌋ - ⌊y - (ej : ℝ) * (x + 1)⌋
        - ⌊((e0 : ℝ) - (ej : ℝ)) * (x + 1) - y⌋
      = ⌊((e0 : ℝ) - 2 * (ej : ℝ)) * x⌋ - ⌊y - (ej : ℝ) * x⌋
        - ⌊((e0 : ℝ) - (ej : ℝ)) * x - y⌋ := by
  have a1 : ⌊((e0 : ℝ) - 2 * (ej : ℝ)) * (x + 1)⌋
      = ⌊((e0 : ℝ) - 2 * (ej : ℝ)) * x⌋ + ((e0 : ℤ) - 2 * (ej : ℤ)) := by
    rw [show ((e0 : ℝ) - 2 * (ej : ℝ)) * (x + 1)
        = ((e0 : ℝ) - 2 * (ej : ℝ)) * x + (((e0 : ℤ) - 2 * (ej : ℤ) : ℤ) : ℝ) by push_cast; ring,
      Int.floor_add_intCast]
  have a2 : ⌊y - (ej : ℝ) * (x + 1)⌋ = ⌊y - (ej : ℝ) * x⌋ - ej := by
    rw [show y - (ej : ℝ) * (x + 1) = (y - (ej : ℝ) * x) - (ej : ℕ) by ring,
      Int.floor_sub_natCast]
  have a3 : ⌊((e0 : ℝ) - (ej : ℝ)) * (x + 1) - y⌋
      = ⌊((e0 : ℝ) - (ej : ℝ)) * x - y⌋ + ((e0 : ℤ) - (ej : ℤ)) := by
    rw [show ((e0 : ℝ) - (ej : ℝ)) * (x + 1) - y
        = (((e0 : ℝ) - (ej : ℝ)) * x - y) + (((e0 : ℤ) - (ej : ℤ) : ℤ) : ℝ) by push_cast; ring,
      Int.floor_add_intCast]
  rw [a1, a2, a3]; ring

theorem expr_nonneg (P : Params) (x y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ phiExpr P x y := by
  unfold phiExpr
  apply add_nonneg
  · exact Finset.sum_nonneg fun j _ => t1_nonneg _ _ _ _ hy0 hy1
  · exact Finset.sum_nonneg fun j _ => t2_nonneg _ _ _ _

theorem expr_per (P : Params) (x : ℝ) : phiExpr P (x + 1) = phiExpr P x := by
  funext y
  unfold phiExpr
  congr 1
  · exact Finset.sum_congr rfl fun j _ => t1_per _ _ _ _
  · exact Finset.sum_congr rfl fun j _ => t2_per _ _ _ _

end Ag4Aux_ZudPhi

theorem solution (P : Params) :
    (∀ x : ℝ, 0 ≤ phi P x) ∧ (∀ x : ℝ, phi P (x + 1) = phi P x) := by
  constructor
  · intro x
    unfold phi
    apply le_csInf
    · exact ⟨_, 0, ⟨le_rfl, one_pos⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact Ag4Aux_ZudPhi.expr_nonneg P x y hy.1 hy.2
  · intro x
    unfold phi
    rw [Ag4Aux_ZudPhi.expr_per]
