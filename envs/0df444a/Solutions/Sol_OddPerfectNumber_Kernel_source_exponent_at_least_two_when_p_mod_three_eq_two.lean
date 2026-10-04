-- Prove2me | solution 1 for OddPerfectNumber.Kernel.source_exponent_at_least_two_when_p_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:53:11.061855+00:00
-- url     : https://prove2.me/submissions/404bee6d-5d27-4fd6-9059-e14b6b0e73d5

import Mathlib

lemma eb54aaab_three_term {r l : Nat} (hr : r.Prime)
    (hr3 : r ≠ 3) (h : r ∣ (1 + l + l ^ 2)) :
    r % 3 = 1 := by
  haveI := Fact.mk hr
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
    exact hr3 this
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

theorem solution {p t m : Nat}
    (hp : p.Prime) (hp3 : p % 3 = 2) (ht : t.Prime) (htd : t ∣ m) (hqp : t != p)
    (hgeom : p ∣ (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i)) :
    2 <= m.factorization t := by
  by_contra hlt
  push_neg at hlt
  have hp1 := hp.two_le
  interval_cases he : m.factorization t
  · simp at hgeom
    omega
  · simp [Finset.sum_range_succ] at hgeom
    have hr3 : p ≠ 3 := by omega
    have := eb54aaab_three_term hp hr3 (by
      have : 1 + t + t ^ 2 = 1 + t + t * t := by ring
      rw [this]; convert hgeom using 1; ring)
    omega
