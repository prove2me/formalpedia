-- Prove2me | solution 1 for OrdinalMSP.Forbidden.integral_eval
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:32:24.988118+00:00
-- url     : https://prove2.me/submissions/ad336a25-81e0-40a7-b16e-6197a055b15b

import Mathlib
set_option autoImplicit false

theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∫ τ in p..1, (p / τ) ^ 1) = -p * Real.log p ∧
      ∀ k : ℕ, 2 ≤ k → (∫ τ in p..1, (p / τ) ^ k) = (p - p ^ k) / ((k : ℝ) - 1) := by
  constructor
  · have h : (∫ τ in p..1, (p / τ) ^ 1) = ∫ τ in p..1, p * τ⁻¹ := by
      refine intervalIntegral.integral_congr (fun τ _ => ?_)
      simp [div_eq_mul_inv]
    rw [h, intervalIntegral.integral_const_mul, integral_inv_of_pos hp0 one_pos]
    simp [Real.log_one]
  · intro k hk
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have h : (∫ τ in p..1, (p / τ) ^ k) = ∫ τ in p..1, p ^ k * τ ^ (-(k : ℤ)) := by
      refine intervalIntegral.integral_congr (fun τ _ => ?_)
      simp [div_eq_mul_inv, mul_pow, zpow_neg]
    rw [h, intervalIntegral.integral_const_mul, integral_zpow]
    · have hne : (p : ℝ) ≠ 0 := hp0.ne'
      have hk1 : ((k : ℝ) - 1) ≠ 0 := by linarith
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      have e : (-((m + 2 : ℕ) : ℤ) + 1) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
      have e1 : (1 : ℝ) ^ (-((m + 2 : ℕ) : ℤ) + 1) = 1 := one_zpow _
      have e2 : p ^ (-((m + 2 : ℕ) : ℤ) + 1) = (p ^ (m + 1))⁻¹ := by
        rw [e, zpow_neg, zpow_natCast]
      have e3 : (((-((m + 2 : ℕ) : ℤ) : ℤ) : ℝ) + 1) = -((m : ℝ) + 1) := by push_cast; ring
      rw [e1, e2, e3]
      have hpm : p ^ (m + 1) ≠ 0 := pow_ne_zero _ hne
      have hm : (((m + 2 : ℕ) : ℝ) - 1) = m + 1 := by push_cast; ring
      rw [hm]
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hp2 : p ^ (m + 2) = p * p ^ (m + 1) := by ring
      rw [hp2]
      field_simp
      ring
    · right
      refine ⟨by omega, ?_⟩
      rw [Set.uIcc_of_le hp1]
      intro h; exact absurd h.1 (not_le.mpr hp0)
