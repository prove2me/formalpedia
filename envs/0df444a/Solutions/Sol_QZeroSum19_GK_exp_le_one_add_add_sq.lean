-- Prove2me | solution 1 for QZeroSum19.GK.exp_le_one_add_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:21:40.532325+00:00
-- url     : https://prove2.me/submissions/5fbaf37a-b827-4985-85de-44f6d6e1c084

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.exp x ≤ 1 + x + 3 * x ^ 2 / 4 := by
  obtain ⟨h1, h2⟩ := hx
  have habs : |x| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
  have hb := Real.exp_bound (x := x) habs (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hb
  have hc : |x| ^ 3 = x ^ 2 * |x| := by
    have : |x| ^ 2 = x ^ 2 := sq_abs x
    calc |x| ^ 3 = |x| ^ 2 * |x| := by ring
      _ = x ^ 2 * |x| := by rw [this]
  have hk : |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * ((Nat.succ 3 : ℕ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ)) : ℝ) := hb
  have hnum : (((Nat.succ 3 : ℕ) : ℝ) / (((Nat.factorial 3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))) = 2 / 9 := by
    norm_num [Nat.factorial]
  rw [hnum, hc] at hk
  have := (abs_le.mp hk).2
  have h3 : x ^ 2 * |x| * (2 / 9) ≤ x ^ 2 / 4 := by
    have : x ^ 2 * |x| ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left habs (sq_nonneg x)
    nlinarith [sq_nonneg x]
  linarith
