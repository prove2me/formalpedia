-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_first_equation_is_a_square
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:21:17.032511+00:00
-- url     : https://prove2.me/submissions/e7e0c1ff-5bd9-42ee-a9be-1c15332daeda

import Mathlib

theorem p5013d85c_no_sq (k m Y : ℕ) (hk : k.Prime) (hY : Y ≠ 0) (h : m ^ 2 = k * Y ^ 2) : False := by
  apply hk.irrational_sqrt
  refine ⟨(m : ℚ) / Y, ?_⟩
  have hYr : (Y : ℝ) ≠ 0 := by exact_mod_cast hY
  have hk' : (k : ℝ) = ((m : ℝ) / Y) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hYr)]
    exact_mod_cast h.symm
  push_cast
  rw [hk', Real.sqrt_sq (by positivity)]

theorem solution (p m d1 q r u a b : Nat)
    (hp : Nat.Prime p) (hd1 : d1 != 0)
    (he : p + 1 = 3 * u ^ 2)
    (hc : p ^ 2 + p + 1 = q * a ^ 2)
    (hd : p ^ 2 - p + 1 = 3 * r * b ^ 2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r))) :
    m = 3 * u * a * b * d1 * q * r := by
  exfalso
  have hd1' : d1 ≠ 0 := by simpa using hd1
  have ha : a ≠ 0 := by rintro rfl; simp at hc
  have hq : q ≠ 0 := by rintro rfl; simp at hc
  have hb : b ≠ 0 := by rintro rfl; simp at hd
  have hr : r ≠ 0 := by rintro rfl; simp at hd
  rcases Nat.even_or_odd u with ⟨v, hv⟩ | hodd
  · have h12 : p + 1 = 2 * (6 * v ^ 2) := by rw [he, hv]; ring
    have hB : (p + 1) / 2 = 6 * v ^ 2 := by
      rw [h12, Nat.mul_div_cancel_left _ two_pos]
    have hv0 : v ≠ 0 := by rintro rfl; simp at h12
    rw [hc, hd, hB] at h1
    have key : m ^ 2 = 2 * (3 * v * a * b * d1 * q * r) ^ 2 := by
      ring_nf at h1 ⊢; linarith
    exact p5013d85c_no_sq 2 m _ Nat.prime_two (by positivity) key
  · have hodd' : Odd (p + 1) := by
      rw [he]; exact (by decide : Odd 3).mul hodd.pow
    have hpe : Even p := by
      rcases Nat.even_or_odd p with h | h
      · exact h
      · exact absurd hodd' (by rw [Nat.not_odd_iff_even]; exact h.add_one)
    have hp2 : p = 2 := hp.even_iff.mp hpe
    subst hp2
    norm_num at h1 hc hd
    have hm : m ^ 2 = 21 * (d1 ^ 2 * (q * r)) := by linarith
    have hrb : r * b ^ 2 = 1 := by
      have : 3 * (r * b ^ 2) = 3 := by rw [← mul_assoc]; exact hd.symm
      omega
    have key : (m * a * b) ^ 2 = 3 * (7 * d1) ^ 2 := by
      calc (m * a * b) ^ 2 = m ^ 2 * a ^ 2 * b ^ 2 := by ring
        _ = 21 * d1 ^ 2 * (q * a ^ 2) * (r * b ^ 2) := by rw [hm]; ring
        _ = 3 * (7 * d1) ^ 2 := by rw [← hc, hrb]; ring
    exact p5013d85c_no_sq 3 _ _ Nat.prime_three (by positivity) key
