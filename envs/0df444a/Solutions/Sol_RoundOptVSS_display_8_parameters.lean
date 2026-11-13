-- Prove2me | solution 1 for RoundOptVSS.display_8_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-13T02:09:57.674869+00:00
-- url     : https://prove2.me/submissions/241baefb-2ebd-4a03-a1c4-5bae1e17dcba

import Mathlib

theorem solution (N n κ hmax δmax q : ℕ) (hq1 : 2 * (hmax + 1) < q)
    (hq2 : 2 ^ (κ + 1) * N * n * (δmax + 1) ≤ q) :
    (q : ℝ) / 2 < (q : ℝ) - hmax - 1 ∧
    (N : ℝ) * n * (1 / ((q : ℝ) - 1) + δmax / ((q : ℝ) - hmax - 1)) ≤ (2 : ℝ) ^ (-(κ : ℤ)) := by
  have h1 : (2 : ℝ) * ((hmax : ℝ) + 1) < q := by exact_mod_cast hq1
  have h2 : (2 : ℝ) ^ (κ + 1) * N * n * ((δmax : ℝ) + 1) ≤ q := by exact_mod_cast hq2
  have hh : (0 : ℝ) ≤ hmax := Nat.cast_nonneg _
  have hδ : (0 : ℝ) ≤ δmax := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hq : (2 : ℝ) < q := by linarith
  have hfirst : (q : ℝ) / 2 < (q : ℝ) - hmax - 1 := by linarith
  refine ⟨hfirst, ?_⟩
  have hκ : (0 : ℝ) < 2 ^ κ := by positivity
  have hpow : (2 : ℝ) ^ (-(κ : ℤ)) = 1 / 2 ^ κ := by
    rw [zpow_neg, zpow_natCast, one_div]
  rw [hpow]
  -- both denominators are at least `q / 2`
  have hA : 1 / ((q : ℝ) - 1) ≤ 2 / q := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  have hB : (δmax : ℝ) / ((q : ℝ) - hmax - 1) ≤ 2 * δmax / q := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hC : (N : ℝ) * n * (1 / ((q : ℝ) - 1) + δmax / ((q : ℝ) - hmax - 1)) ≤
      (N : ℝ) * n * (2 * (δmax + 1) / q) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hN hn)
    have : 2 * ((δmax : ℝ) + 1) / q = 2 / q + 2 * δmax / q := by ring
    rw [this]; linarith
  refine hC.trans ?_
  rw [mul_div_assoc', div_le_div_iff₀ (by linarith) hκ]
  have : (2 : ℝ) ^ (κ + 1) = 2 * 2 ^ κ := by ring
  rw [this] at h2
  nlinarith
