-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat22_semigroup_rat_exp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:05:34.05135+00:00
-- url     : https://prove2.me/submissions/66065cb1-f882-420e-a57e-5968efddf523

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

/-- The fourth phase of LeanLevy's marginal characteristic-function factorisation:
exponential representation at nonnegative rational times. -/
theorem solution
    (φ : ℝ≥0 → ℂ) (δ : ℝ≥0) (c : ℂ) (N : ℕ)
    (hN_pos : 0 < N) (hN_small : (1 : ℝ≥0) / (N : ℝ≥0) < δ)
    (hφ_ne : ∀ t, φ t ≠ 0)
    (hφ_pow : ∀ (n : ℕ) (s : ℝ≥0),
      φ ((n : ℝ≥0) * s) = (φ s) ^ n)
    (hφ_rat : ∀ (k n : ℕ),
      φ ((k : ℝ≥0) / (n : ℝ≥0)) = (φ (1 / (n : ℝ≥0))) ^ k)
    (hconst : ∀ n : ℕ, 0 < n → (1 : ℝ≥0) / (n : ℝ≥0) < δ →
      ↑(n : ℤ) * log (φ (1 / (n : ℝ≥0))) = c) :
    ∀ (k n : ℕ), 0 < n →
      φ ((k : ℝ≥0) / (n : ℝ≥0)) =
        exp (c * ↑((k : ℝ) / (n : ℝ))) := by
  have hφ_inv_exp : ∀ n : ℕ, 0 < n →
      φ (1 / (n : ℝ≥0)) = exp (c / ↑(n : ℕ)) := by
    intro n hn
    have hn_ne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hN_ne : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnN_pos : 0 < n * N := Nat.mul_pos hn hN_pos
    have hnN_ne : (n * N : ℕ) ≠ 0 := by omega
    have hnN_small : (1 : ℝ≥0) / ((n * N : ℕ) : ℝ≥0) < δ :=
      lt_of_le_of_lt
        (one_div_le_one_div_of_le (Nat.cast_pos.mpr hN_pos)
          (by exact_mod_cast Nat.le_mul_of_pos_left N hn))
        hN_small
    have hlog_nN := hconst (n * N) hnN_pos hnN_small
    have hφ_nN : φ (1 / ((n * N : ℕ) : ℝ≥0)) =
        exp (c / ↑(n * N : ℕ)) := by
      rw [← exp_log (hφ_ne _)]; congr 1
      have hne : (↑(n * N : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr hnN_ne
      have hmul : (↑(n * N : ℕ) : ℂ) *
          log (φ (1 / ↑(n * N))) = c := by exact_mod_cast hlog_nN
      rw [mul_comm] at hmul
      exact (div_eq_of_eq_mul hne hmul.symm).symm
    have hNnN : (N : ℝ≥0) * (1 / ((n * N : ℕ) : ℝ≥0)) =
        1 / (n : ℝ≥0) := by
      rw [Nat.cast_mul, one_div, one_div]
      rw [show (↑n * ↑N : ℝ≥0)⁻¹ = (↑N)⁻¹ * (↑n)⁻¹ from mul_inv_rev _ _,
          ← mul_assoc, mul_inv_cancel₀ hN_ne, one_mul]
    rw [← hNnN, hφ_pow N, hφ_nN, ← exp_nat_mul]; congr 1
    push_cast [Nat.cast_mul]
    field_simp [show (n : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (by omega),
                show (N : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (by omega)]
  intro k n hn
  rw [hφ_rat k n, hφ_inv_exp n hn, ← exp_nat_mul]; congr 1
  push_cast
  field_simp [show (n : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (by omega)]
