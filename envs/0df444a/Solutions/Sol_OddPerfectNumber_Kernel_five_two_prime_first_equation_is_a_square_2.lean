-- Prove2me | solution 2 for OddPerfectNumber.Kernel.five_two_prime_first_equation_is_a_square
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T20:07:52.811264+00:00
-- url     : https://prove2.me/submissions/e7e50750-e826-4361-89ae-9e995c5de248

import Mathlib
theorem solution (p m d1 q r u a b : Nat)
    (hp : Nat.Prime p) (hd1 : d1 != 0)
    (he : p + 1 = 3 * u ^ 2)
    (hc : p ^ 2 + p + 1 = q * a ^ 2)
    (hd : p ^ 2 - p + 1 = 3 * r * b ^ 2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r))) :
    m = 3 * u * a * b * d1 * q * r := by
  have key : ∀ (l y z : Nat), l.Prime → l * y ^ 2 = z ^ 2 → y = 0 := by
    intro l y z hl h
    by_contra hy
    have hz : z ≠ 0 := by
      rintro rfl
      simp [hl.ne_zero, hy] at h
    have := congrArg (fun n => n.factorization l) h
    simp [Nat.factorization_mul hl.ne_zero (pow_ne_zero 2 hy), Nat.factorization_pow,
      hl.factorization_self] at this
    omega
  have hd1' : d1 ≠ 0 := by simpa using hd1
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exfalso
    norm_num at he hc hd h1
    have hrb : r * b ^ 2 = 1 := by nlinarith
    have hm : m ^ 2 = 21 * (d1 ^ 2 * (q * r)) := by omega
    have : 3 * (7 * d1) ^ 2 = (m * a * b) ^ 2 := by
      have : (m * a * b) ^ 2 = m ^ 2 * (a ^ 2 * b ^ 2) := by ring
      rw [this, hm]
      have e : 21 * (d1 ^ 2 * (q * r)) * (a ^ 2 * b ^ 2) = 21 * d1 ^ 2 * (q * a ^ 2) * (r * b ^ 2) := by ring
      rw [e, ← hc, hrb]; ring
    have := key 3 _ _ Nat.prime_three this
    omega
  · obtain ⟨k, hk⟩ := hodd
    have hB : (p + 1) / 2 = k + 1 := by omega
    have h2B : 2 * (k + 1) = 3 * u ^ 2 := by omega
    rw [hB, hc, hd] at h1
    have h3 : 2 * m ^ 2 = (3 * u * a * b * d1 * q * r) ^ 2 := by
      have e : (3 * u * a * b * d1 * q * r) ^ 2 = q * a ^ 2 * (2 * (k + 1)) * (3 * r * b ^ 2) * (d1 ^ 2 * (q * r)) := by
        rw [h2B]; ring
      rw [e]
      have : 2 * q * a ^ 2 * (k + 1) * (3 * r * b ^ 2) * (d1 ^ 2 * (q * r)) = 2 * m ^ 2 := by
        rw [h1]; ring
      linarith
    have hm := key 2 _ _ Nat.prime_two h3
    subst hm
    have h0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h3.symm
    rw [h0]
