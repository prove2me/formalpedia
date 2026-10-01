-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_cyclotomic_primes_dvd_m
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:19:31.19129+00:00
-- url     : https://prove2.me/submissions/5a3f156d-da73-44fa-a0fe-1eabc5a20431

import Mathlib

theorem solution (p m d1 q r : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime) (hr : r.Prime)
    (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r)))
    (hsq : ∃ y : Nat, y ^ 2 = q * r * (p ^ 2 + p + 1) *
      ((p + 1) / 2 * (p ^ 2 - p + 1))) :
    q ∣ m ∧ r ∣ m := by
  have heq : m ^ 2 = (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) *
      (d1 ^ 2 * (q * r)) := by
    apply mul_left_cancel₀ (by decide : (2 : Nat) ≠ 0)
    calc
      2 * m ^ 2 = _ := h1
      _ = _ := by ring
  have hqdiv : q ∣ m ^ 2 := by
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right q r) _) _
  have hrdiv : r ∣ m ^ 2 := by
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_left r q) _) _
  exact ⟨hq.dvd_of_dvd_pow hqdiv, hr.dvd_of_dvd_pow hrdiv⟩
