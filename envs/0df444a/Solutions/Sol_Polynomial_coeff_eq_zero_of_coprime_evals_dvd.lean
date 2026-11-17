-- Prove2me | solution 1 for Polynomial.coeff_eq_zero_of_coprime_evals_dvd
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:11.927846+00:00
-- url     : https://prove2.me/submissions/372e46f7-87a1-4ccc-9dcb-92bcfadfd217

import Mathlib

set_option autoImplicit false

namespace Polynomial

/-- Four coprime evaluation bases extract vanishing low coefficients when their product
strictly exceeds the absolute values of those coefficients. -/
theorem _root_.solution
    (p : ℤ[X]) (N : ℕ) (b₀ b₁ b₂ b₃ : ℤ)
    (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃)
    (hcop₀₁ : IsCoprime b₀ b₁)
    (hcop₂ : IsCoprime (b₀ * b₁) b₂)
    (hcop₃ : IsCoprime (b₀ * b₁ * b₂) b₃)
    (hbound : ∀ i : ℕ, i < N → |p.coeff i| < b₀ * b₁ * b₂ * b₃)
    (heval₀ : b₀ ^ N ∣ p.eval b₀) (heval₁ : b₁ ^ N ∣ p.eval b₁)
    (heval₂ : b₂ ^ N ∣ p.eval b₂) (heval₃ : b₃ ^ N ∣ p.eval b₃) :
    ∀ i : ℕ, i < N → p.coeff i = 0 := by
  have hprod : 0 < b₀ * b₁ * b₂ * b₃ := mul_pos (mul_pos (mul_pos hb₀ hb₁) hb₂) hb₃
  induction N generalizing p with
  | zero =>
      intro i hi
      omega
  | succ N ih =>
      have constant_dvd (b : ℤ) (heval : b ^ (N + 1) ∣ p.eval b) : b ∣ p.coeff 0 := by
        have hdiv : b ∣ p.eval b :=
          dvd_trans (dvd_pow_self b (by omega)) heval
        have hdiff : b ∣ p.eval b - p.eval 0 := by
          simpa using sub_dvd_eval_sub b 0 p
        simpa [coeff_zero_eq_eval_zero] using dvd_sub hdiv hdiff
      have hcdiv : b₀ * b₁ * b₂ * b₃ ∣ p.coeff 0 :=
        hcop₃.mul_dvd
          (hcop₂.mul_dvd
            (hcop₀₁.mul_dvd (constant_dvd b₀ heval₀) (constant_dvd b₁ heval₁))
            (constant_dvd b₂ heval₂))
          (constant_dvd b₃ heval₃)
      have hc0 : p.coeff 0 = 0 := by
        obtain ⟨z, hz⟩ := hcdiv
        have hsmall := hbound 0 (by omega)
        rw [hz, abs_mul, abs_of_pos hprod] at hsmall
        by_cases hz0 : z = 0
        · simp [hz, hz0]
        · have hzlarge : 1 ≤ |z| := by
            have := abs_pos.mpr hz0
            omega
          have hle : b₀ * b₁ * b₂ * b₃ ≤ b₀ * b₁ * b₂ * b₃ * |z| := by
            simpa using mul_le_mul_of_nonneg_left hzlarge (le_of_lt hprod)
          omega
      obtain ⟨q, hpq⟩ := X_dvd_iff.mpr hc0
      have hqbound : ∀ i : ℕ, i < N → |q.coeff i| < b₀ * b₁ * b₂ * b₃ := by
        intro i hi
        simpa [hpq, coeff_X_mul] using hbound (i + 1) (by omega)
      have cancel_eval (b : ℤ) (hb : b ≠ 0)
          (heval : b ^ (N + 1) ∣ p.eval b) : b ^ N ∣ q.eval b := by
        obtain ⟨z, hz⟩ := heval
        have hcancel : b * q.eval b = b * (b ^ N * z) := by
          simpa [hpq, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hz
        exact ⟨z, mul_left_cancel₀ hb hcancel⟩
      intro i hi
      cases i with
      | zero => exact hc0
      | succ i =>
          simpa [hpq, coeff_X_mul] using
            ih q hqbound
              (cancel_eval b₀ (ne_of_gt hb₀) heval₀)
              (cancel_eval b₁ (ne_of_gt hb₁) heval₁)
              (cancel_eval b₂ (ne_of_gt hb₂) heval₂)
              (cancel_eval b₃ (ne_of_gt hb₃) heval₃) i (by omega)

end Polynomial
