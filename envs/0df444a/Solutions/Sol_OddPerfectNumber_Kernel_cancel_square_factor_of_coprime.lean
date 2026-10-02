-- Prove2me | solution 1 for OddPerfectNumber.Kernel.cancel_square_factor_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T20:04:54.1669+00:00
-- url     : https://prove2.me/submissions/4e7a7505-955d-4a3c-8da9-5fb5d64783b8

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

theorem solution {a b c x y : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc : c.Prime) (hab : a.Coprime b) (hax : a = c * x ^ 2) (hy : a * b = c * y ^ 2) :
    exists z : Nat, z ^ 2 = b := by
  have hc0 : c ≠ 0 := hc.ne_zero
  have h_prod : c * (x ^ 2 * b) = c * y ^ 2 := by
    calc c * (x ^ 2 * b) = (c * x ^ 2) * b := by ring
    _ = a * b := by rw [← hax]
    _ = c * y ^ 2 := hy
  have h_eq : x ^ 2 * b = y ^ 2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) h_prod
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by decide : 2 ≠ 0), mul_zero] at hax
    exact ha0 hax
  have hdvd_int : (x : ℤ) ^ 2 ∣ (y : ℤ) ^ 2 := by
    use (b : ℤ)
    exact_mod_cast h_eq.symm
  have hdvd_z : (x : ℤ) ∣ (y : ℤ) := (Int.pow_dvd_pow_iff (by decide)).mp hdvd_int
  have hdvd : x ∣ y := by exact_mod_cast hdvd_z
  obtain ⟨z, hz⟩ := hdvd
  have hy_sq : y ^ 2 = x ^ 2 * z ^ 2 := by
    rw [hz]
    ring
  have h_sq : x ^ 2 * z ^ 2 = x ^ 2 * b := by
    rw [← hy_sq, ← h_eq]
  have hx2_pos : 0 < x ^ 2 := by positivity
  have hz_eq : z ^ 2 = b := Nat.eq_of_mul_eq_mul_left hx2_pos h_sq
  exact ⟨z, hz_eq⟩
