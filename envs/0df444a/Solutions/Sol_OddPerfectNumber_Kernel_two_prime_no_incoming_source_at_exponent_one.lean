-- Prove2me | solution 1 for OddPerfectNumber.Kernel.two_prime_no_incoming_source_at_exponent_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:53:18.709985+00:00
-- url     : https://prove2.me/submissions/85b9fdbf-b3d1-4a9c-b4ed-e05074a04d3c

import Mathlib

set_option autoImplicit false

theorem e9d_mod12 (p m d1 q r : Nat)
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m)
    (hpm : Not (Dvd.dvd p m)) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hq3 : q != 3) (hr3 : r != 3)
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    p % 12 = 5 := by
  have hq3' : q ≠ 3 := by simpa using hq3
  have hr3' : r ≠ 3 := by simpa using hr3
  -- p % 3 ≠ 0 since p prime and p ≠ 3 (p % 4 = 1)
  have hp3 : p % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    omega
  by_contra hne
  have hp31 : p % 3 = 1 := by omega
  have hm0 : m ≠ 0 := by
    rintro rfl; exact (Nat.not_even_iff_odd.mpr hm) (by decide)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- the factors
  have hs : p ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hsq3 : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hp31]
  have hsq9 : p ^ 2 % 9 = 1 ∧ p % 9 = 1 ∨ p ^ 2 % 9 = 7 ∧ p % 9 = 4 ∨ p ^ 2 % 9 = 4 ∧ p % 9 = 7 := by
    have : p % 9 = 1 ∨ p % 9 = 4 ∨ p % 9 = 7 := by omega
    rcases this with h | h | h
    · left; exact ⟨by rw [Nat.pow_mod, h], h⟩
    · right; left; exact ⟨by rw [Nat.pow_mod, h], h⟩
    · right; right; exact ⟨by rw [Nat.pow_mod, h], h⟩
  have hC0 : p ^ 2 + p + 1 ≠ 0 := by omega
  have hB0 : (p + 1) / 2 ≠ 0 := by omega
  have hD0 : p ^ 2 - p + 1 ≠ 0 := by omega
  have hq0 : q ≠ 0 := hq.ne_zero
  have hr0 : r ≠ 0 := hr.ne_zero
  have hd0 : d1 ≠ 0 := by
    rintro rfl
    simp at h1
    exact hm0 h1
  have vC : padicValNat 3 (p ^ 2 + p + 1) = 1 := by
    have h1' : 3 ^ 1 ∣ p ^ 2 + p + 1 := by
      have : (p ^ 2 + p + 1) % 3 = 0 := by omega
      simpa using Nat.dvd_of_mod_eq_zero this
    have h2' : ¬ 3 ^ 2 ∣ p ^ 2 + p + 1 := by
      intro h
      have := Nat.mod_eq_zero_of_dvd h
      norm_num at this
      omega
    have a := (padicValNat_dvd_iff_le hC0).mp h1'
    have b : ¬ 2 ≤ padicValNat 3 (p ^ 2 + p + 1) := fun hh =>
      h2' ((padicValNat_dvd_iff_le hC0).mpr hh)
    omega
  have vB : padicValNat 3 ((p + 1) / 2) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    omega
  have vD : padicValNat 3 (p ^ 2 - p + 1) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    omega
  have v2 : padicValNat 3 2 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd; omega
  have vq : padicValNat 3 q = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    exact hq3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h).symm
  have vr : padicValNat 3 r = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    exact hr3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h).symm
  have hL : padicValNat 3 (2 * m ^ 2) = 2 * padicValNat 3 m := by
    rw [padicValNat.mul (by norm_num) (pow_ne_zero _ hm0), padicValNat.pow m 2, v2]
    ring
  have hR : padicValNat 3 ((2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
      = 1 + 2 * padicValNat 3 d1 := by
    rw [padicValNat.mul (mul_ne_zero (mul_ne_zero two_ne_zero hC0) (mul_ne_zero hB0 hD0))
        (mul_ne_zero (pow_ne_zero _ hd0) (mul_ne_zero hq0 hr0)),
      padicValNat.mul (mul_ne_zero two_ne_zero hC0) (mul_ne_zero hB0 hD0),
      padicValNat.mul (by norm_num) hC0,
      padicValNat.mul hB0 hD0,
      padicValNat.mul (pow_ne_zero _ hd0) (mul_ne_zero hq0 hr0),
      padicValNat.mul hq0 hr0, padicValNat.pow d1 2, v2, vC, vB, vD, vq, vr]
    ring
  rw [h1, hR] at hL
  omega

theorem e9d_mod3 {r l : Nat} (hr : r.Prime)
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


theorem solution {p m d1 q r t : Nat}
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m)
    (hpm : Not (Dvd.dvd p m)) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hq3 : q != 3) (hr3 : r != 3)
    (ht : t.Prime) (htd : Dvd.dvd t m) (htp : t != p)
    (hte : m.factorization t = 1)
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (hgeom : Dvd.dvd p (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i)) :
    False := by
  have h12 := e9d_mod12 p m d1 q r hp hp2 hp4 hm hpm hq hr hqr hq3 hr3 h1
  rw [hte] at hgeom
  have hs : (∑ i ∈ Finset.range (2 * 1 + 1), t ^ i) = 1 + t + t ^ 2 := by
    simp [Finset.sum_range_succ]
  rw [hs] at hgeom
  have hp3 : p != 3 := by
    simp only [bne_iff_ne, ne_eq]; omega
  have := e9d_mod3 hp hp3 hgeom
  omega
