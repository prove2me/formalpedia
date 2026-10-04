-- Prove2me | solution 1 for OddPerfectNumber.Kernel.prime_dvd_three_term_sum_ne_three_gives_one_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:19:25.728505+00:00
-- url     : https://prove2.me/submissions/6fe00e91-2f7c-4fc9-b38c-751172f5aa94

import Mathlib

theorem solution {r l : Nat} (hr : r.Prime)
    (hr3 : r != 3) (h : Dvd.dvd r (1 + l + l ^ 2)) :
    r % 3 = 1 := by
  haveI := Fact.mk hr
  have hr3' : r ≠ 3 := by simpa using hr3
  have h0 : ((1 + l + l ^ 2 : ℕ) : ZMod r) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact h
  push_cast at h0
  set x : ZMod r := (l : ZMod r) with hx
  have hx3 : x ^ 3 = 1 := by
    have : x ^ 3 - 1 = (x - 1) * (1 + x + x ^ 2) := by ring
    rw [h0, mul_zero, sub_eq_zero] at this
    exact this
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1] at h0
    have h3 : ((3 : ℕ) : ZMod r) = 0 := by push_cast; linear_combination h0
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
    exact hr3' this
  have hx0 : x ≠ 0 := by
    intro h1
    rw [h1] at hx3
    norm_num at hx3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd := ZMod.orderOf_dvd_card_sub_one hx0
  rw [hord] at hdvd
  have h2 := hr.two_le
  omega
