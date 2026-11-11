-- Prove2me | solution 1 for RobustFracMP.fact_2_1
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-10T10:50:43.440922+00:00
-- url     : https://prove2.me/submissions/966557c1-ff1f-4a9c-8ea1-877da3773a3e

import Mathlib

set_option autoImplicit false

/-- The elementary inequality `(a + b)^(k+1) ≤ 2^k (a^(k+1) + b^(k+1))` for `a, b ≥ 0`. -/
private theorem add_pow_succ_le (k : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (k + 1) ≤ 2 ^ k * (a ^ (k + 1) + b ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- `(a - b)` and `(a^(k+1) - b^(k+1))` have the same sign
    have h3 : 0 ≤ (a - b) * (a ^ (k + 1) - b ^ (k + 1)) := by
      rcases le_total a b with h | h
      · have := pow_le_pow_left₀ ha h (k + 1)
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have := pow_le_pow_left₀ hb h (k + 1)
        exact mul_nonneg (by linarith) (by linarith)
    have h2 : (a + b) * (a ^ (k + 1) + b ^ (k + 1)) ≤ 2 * (a ^ (k + 2) + b ^ (k + 2)) := by
      have e : 2 * (a ^ (k + 2) + b ^ (k + 2)) - (a + b) * (a ^ (k + 1) + b ^ (k + 1))
          = (a - b) * (a ^ (k + 1) - b ^ (k + 1)) := by ring
      linarith
    calc (a + b) ^ (k + 1 + 1) = (a + b) * (a + b) ^ (k + 1) := by ring
      _ ≤ (a + b) * (2 ^ k * (a ^ (k + 1) + b ^ (k + 1))) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = 2 ^ k * ((a + b) * (a ^ (k + 1) + b ^ (k + 1))) := by ring
      _ ≤ 2 ^ k * (2 * (a ^ (k + 2) + b ^ (k + 2))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ (k + 1) * (a ^ (k + 1 + 1) + b ^ (k + 1 + 1)) := by ring

theorem solution {P : Type*} [MetricSpace P] (z : ℕ) (hz : 1 ≤ z) (p q t : P) :
    dist p q ^ z ≤ 2 ^ (z - 1) * (dist p t ^ z + dist t q ^ z) := by
  obtain ⟨k, rfl⟩ : ∃ k, z = k + 1 := ⟨z - 1, by omega⟩
  calc dist p q ^ (k + 1) ≤ (dist p t + dist t q) ^ (k + 1) :=
        pow_le_pow_left₀ dist_nonneg (dist_triangle p t q) _
    _ ≤ 2 ^ k * (dist p t ^ (k + 1) + dist t q ^ (k + 1)) :=
        add_pow_succ_le k _ _ dist_nonneg dist_nonneg
    _ = 2 ^ (k + 1 - 1) * (dist p t ^ (k + 1) + dist t q ^ (k + 1)) := by simp
