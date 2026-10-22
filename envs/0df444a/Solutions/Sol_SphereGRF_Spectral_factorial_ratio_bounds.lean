-- Prove2me | solution 1 for SphereGRF.Spectral.factorial_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:21:44.256619+00:00
-- url     : https://prove2.me/submissions/bf4efff1-2924-4a8d-a26c-c9325100ac32

import Mathlib

theorem solution (n : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ℓ : ℕ, n ≤ ℓ →
      c₁ * (ℓ : ℝ) ^ (2 * n) ≤ ((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ) ∧
      ((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ) ≤ c₂ * (ℓ : ℝ) ^ (2 * n) := by
  refine ⟨1 / ((2 * n + 1 : ℝ) ^ (2 * n)), 4 ^ n, by positivity, by positivity, ?_⟩
  intro ℓ hℓ
  have hsub : ℓ + n - 2 * n = ℓ - n := by omega
  have hle : 2 * n ≤ ℓ + n := by omega
  have hfac := Nat.factorial_mul_descFactorial hle
  rw [hsub] at hfac
  have hpos : (0 : ℝ) < ((ℓ - n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hratio : ((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ) =
      ((ℓ + n).descFactorial (2 * n) : ℝ) := by
    rw [div_eq_iff hpos.ne', ← hfac]; push_cast; ring
  rw [hratio]
  have hlow : ((ℓ + n + 1 - 2 * n) ^ (2 * n) : ℕ) ≤ (ℓ + n).descFactorial (2 * n) :=
    Nat.pow_sub_le_descFactorial _ _
  have hup : (ℓ + n).descFactorial (2 * n) ≤ (ℓ + n) ^ (2 * n) := Nat.descFactorial_le_pow _ _
  have e1 : ℓ + n + 1 - 2 * n = ℓ - n + 1 := by omega
  rw [e1] at hlow
  have hlowR : ((ℓ - n + 1 : ℕ) : ℝ) ^ (2 * n) ≤ ((ℓ + n).descFactorial (2 * n) : ℝ) := by
    exact_mod_cast hlow
  have hupR : ((ℓ + n).descFactorial (2 * n) : ℝ) ≤ ((ℓ + n : ℕ) : ℝ) ^ (2 * n) := by
    exact_mod_cast hup
  have hℓR : (n : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  constructor
  · refine le_trans ?_ hlowR
    have hb : (ℓ : ℝ) / (2 * n + 1) ≤ ((ℓ - n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub hℓ, Nat.cast_one, div_le_iff₀ (by positivity)]
      nlinarith
    calc 1 / ((2 * n + 1 : ℝ) ^ (2 * n)) * (ℓ : ℝ) ^ (2 * n)
        = ((ℓ : ℝ) / (2 * n + 1)) ^ (2 * n) := by rw [div_pow]; ring
      _ ≤ ((ℓ - n + 1 : ℕ) : ℝ) ^ (2 * n) := pow_le_pow_left₀ (by positivity) hb _
  · refine le_trans hupR ?_
    have hb : ((ℓ + n : ℕ) : ℝ) ≤ 2 * ℓ := by push_cast; linarith
    calc ((ℓ + n : ℕ) : ℝ) ^ (2 * n) ≤ (2 * (ℓ : ℝ)) ^ (2 * n) :=
          pow_le_pow_left₀ (by positivity) hb _
      _ = 4 ^ n * (ℓ : ℝ) ^ (2 * n) := by rw [mul_pow, pow_mul]; norm_num
