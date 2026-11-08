-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat22_semigroup_log_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:12:56.188923+00:00
-- url     : https://prove2.me/submissions/8a86498b-b3e4-4c20-afce-90acc7857e83

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

/-- The exponent extracted from sufficiently small natural reciprocals is independent
of the chosen reciprocal. This is the third analytic phase of LeanLevy's proof. -/
theorem solution
    (φ : ℝ≥0 → ℂ) (δ : ℝ≥0) (hδ_pos : 0 < δ)
    (hlog_pow : ∀ (n : ℕ) (s : ℝ≥0), (n : ℝ≥0) * s < δ →
      log (φ ((n : ℝ≥0) * s)) = ↑(n : ℤ) * log (φ s)) :
    ∃ c : ℂ, ∀ n : ℕ, 0 < n → (1 : ℝ≥0) / (n : ℝ≥0) < δ →
      ↑(n : ℤ) * log (φ (1 / (n : ℝ≥0))) = c := by
  obtain ⟨N, hN_pos, hN_small⟩ :
      ∃ N : ℕ, 0 < N ∧ (1 : ℝ≥0) / (N : ℝ≥0) < δ := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((δ : ℝ)⁻¹)
    have hn_pos : 0 < n := by
      exact_mod_cast lt_trans (inv_pos.mpr (by positivity : (0 : ℝ) < δ)) hn
    refine ⟨n, hn_pos, ?_⟩
    rw [show (1 : ℝ≥0) / (n : ℝ≥0) < δ ↔
      ((1 : ℝ) / (n : ℝ) < (δ : ℝ)) from by
        rw [← NNReal.coe_lt_coe]; simp]
    rw [one_div]
    calc (↑n : ℝ)⁻¹ = 1 / ↑n := (one_div _).symm
      _ < 1 / (δ : ℝ)⁻¹ :=
          one_div_lt_one_div_of_lt
            (inv_pos.mpr (by positivity : (0 : ℝ) < ↑δ)) hn
      _ = ↑δ := by rw [one_div, inv_inv]
  refine ⟨↑(N : ℤ) * log (φ (1 / (N : ℝ≥0))), ?_⟩
  intro n hn hn_lt
  have hn_ne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN_ne : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNnN : (N : ℝ≥0) * (1 / ((n * N : ℕ) : ℝ≥0)) =
      1 / (n : ℝ≥0) := by
    rw [Nat.cast_mul, one_div, one_div]
    rw [show (↑n * ↑N : ℝ≥0)⁻¹ = (↑N)⁻¹ * (↑n)⁻¹ from mul_inv_rev _ _,
        ← mul_assoc, mul_inv_cancel₀ hN_ne, one_mul]
  have hnnN : (n : ℝ≥0) * (1 / ((n * N : ℕ) : ℝ≥0)) =
      1 / (N : ℝ≥0) := by
    rw [Nat.cast_mul, one_div, one_div]
    rw [show (↑n * ↑N : ℝ≥0)⁻¹ = (↑N)⁻¹ * (↑n)⁻¹ from mul_inv_rev _ _,
        mul_comm (↑N : ℝ≥0)⁻¹, ← mul_assoc, mul_inv_cancel₀ hn_ne, one_mul]
  have h1 := hlog_pow N (1 / ((n * N : ℕ) : ℝ≥0))
    (by rw [hNnN]; exact hn_lt)
  rw [hNnN] at h1
  have h2 := hlog_pow n (1 / ((n * N : ℕ) : ℝ≥0))
    (by rw [hnnN]; exact hN_small)
  rw [hnnN] at h2
  calc ↑(n : ℤ) * log (φ (1 / (n : ℝ≥0)))
      = ↑(n : ℤ) *
        (↑(N : ℤ) * log (φ (1 / ((n * N : ℕ) : ℝ≥0)))) := by rw [h1]
    _ = ↑(N : ℤ) *
        (↑(n : ℤ) * log (φ (1 / ((n * N : ℕ) : ℝ≥0)))) := by ring
    _ = ↑(N : ℤ) * log (φ (1 / (N : ℝ≥0))) := by rw [h2]
