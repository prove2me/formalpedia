-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_R__sub_one_isUnit_29a9b3d1283b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:45.662856+00:00
-- url     : https://prove2.me/submissions/71283a1a-4bd7-4de9-8f5f-a0e3d85b39c6

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : α ≠ -1) :
    IsUnit (Rα n α - 1) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  -- det(R_α - I) = det(1 • R_α + (-1) • I) = (-1)^n * α + (-1)^n = (-1)^n * (α + 1)
  have hdet : (Rα n α - 1).det = (-1)^n * α + (-1)^n := by
    have h2 := det_xRα_add_yI n hn 1 (-1) α
    simp only [one_smul, neg_one_smul, sub_eq_add_neg] at h2 ⊢
    exact h2
  rw [hdet, isUnit_iff_ne_zero]
  -- (-1)^n * (α + 1) ≠ 0 since (-1)^n ≠ 0 and α + 1 ≠ 0
  intro h
  have hfactor : (-1 : ℝ)^n * α + (-1)^n = (-1)^n * (α + 1) := by ring
  rw [hfactor] at h
  have hpow_ne : (-1 : ℝ)^n ≠ 0 := by
    rcases neg_one_pow_eq_or ℝ n with hp | hp <;> simp [hp]
  have hα1 : α + 1 = 0 := (mul_eq_zero.mp h).resolve_left hpow_ne
  exact hα (by linarith)
end GroupTheoreticShannonCapacity.MAlpha
