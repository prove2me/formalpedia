-- Prove2me | solution 1 for OddPerfectNumber.Kernel.coprime_non_square_blocks_prime_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:12:09.043786+00:00
-- url     : https://prove2.me/submissions/476c1bb6-af7d-423a-bb28-2f722acbbf42

import Mathlib

lemma prime_square_left {a b c y : Nat} (hc : c.Prime) (hab : a.Coprime b)
    (hy : a * b = c * y ^ 2) (hca : c ∣ a) : ∃ x : Nat, a = c * x ^ 2 := by
  obtain ⟨k, rfl⟩ := hca
  have hcop : k.Coprime b := hab.of_dvd_left (dvd_mul_left k c)
  have hunit : IsUnit (gcd k b) := by
    change IsUnit (Nat.gcd k b)
    rw [hcop.gcd_eq_one]
    exact isUnit_one
  have hkb : k * b = y ^ 2 := by
    apply mul_left_cancel₀ hc.ne_zero
    simpa only [mul_assoc] using hy
  obtain ⟨x, hx⟩ := exists_eq_pow_of_mul_eq_pow hunit hkb
  exact ⟨x, by rw [hx]⟩

theorem solution {a b c y : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc : c.Prime) (hab : a.Coprime b) (hna : ¬ ∃ w : Nat, w ^ 2 = a)
    (hnb : ¬ ∃ w : Nat, w ^ 2 = b) (hy : a * b = c * y ^ 2) :
    (∃ x : Nat, a = c * x ^ 2) ∨ (∃ x : Nat, b = c * x ^ 2) := by
  have hcab : c ∣ a * b := by rw [hy]; exact dvd_mul_right c (y ^ 2)
  rcases hc.dvd_mul.mp hcab with hca | hcb
  · exact Or.inl (prime_square_left hc hab hy hca)
  · exact Or.inr (prime_square_left hc hab.symm (by simpa [mul_comm a b] using hy) hcb)
