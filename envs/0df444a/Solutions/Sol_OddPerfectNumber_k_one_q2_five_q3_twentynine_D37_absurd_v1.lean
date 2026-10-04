-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D37_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T08:20:31.656988+00:00
-- url     : https://prove2.me/submissions/9a970ad6-9aa2-4823-8341-ad7650eeb5d3

import Mathlib

set_option autoImplicit false

namespace P9aacc79dAux

lemma pow_eq_one_of_dvd_geom (p q n : ℕ) (h : p ∣ ∑ i ∈ Finset.range n, q ^ i) :
    ((q : ZMod p)) ^ n = 1 := by
  have h0 : ((∑ i ∈ Finset.range n, q ^ i : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 h
  push_cast at h0
  have h1 := geom_sum_mul (q : ZMod p) n
  rw [h0, zero_mul] at h1
  exact (sub_eq_zero.1 h1.symm)

lemma not_dvd_of_neg_one (q k n : ℕ) (hk : ((q : ZMod 73)) ^ k = -1) (hn : Odd n)
    (h : 73 ∣ ∑ i ∈ Finset.range n, q ^ i) : False := by
  have h1 := pow_eq_one_of_dvd_geom 73 q n h
  have h2 : (((q : ZMod 73)) ^ k) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
  rw [hk, hn.neg_one_pow] at h2
  exact absurd h2 (by decide)

lemma three_ne (a : ℕ) (h : 73 ∣ ∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) : False :=
  not_dvd_of_neg_one 3 6 _ (by decide) (odd_two_mul_add_one a) h

lemma five_ne (a : ℕ) (h : 73 ∣ ∑ i ∈ Finset.range (2 * a + 1), 5 ^ i) : False :=
  not_dvd_of_neg_one 5 36 _ (by decide) (odd_two_mul_add_one a) h

lemma twentynine_ne (a : ℕ) (h : 73 ∣ ∑ i ∈ Finset.range (2 * a + 1), 29 ^ i) : False :=
  not_dvd_of_neg_one 29 36 _ (by decide) (odd_two_mul_add_one a) h

lemma thirtyseven_127 (n : ℕ) (h : 73 ∣ ∑ i ∈ Finset.range n, 37 ^ i) :
    127 ∣ ∑ i ∈ Finset.range n, 37 ^ i := by
  have h1 := pow_eq_one_of_dvd_geom 73 37 n h
  have hn : n = 9 * (n / 9) + n % 9 := (Nat.div_add_mod n 9).symm
  have h9 : ((37 : ℕ) : ZMod 73) ^ 9 = 1 := by decide
  have hr : ((37 : ℕ) : ZMod 73) ^ (n % 9) = 1 := by
    rw [hn, pow_add, pow_mul, h9, one_pow, one_mul] at h1
    simpa [Nat.add_mod] using h1
  have hlt : n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hr0 : n % 9 = 0 := by
    generalize n % 9 = r at hr hlt
    interval_cases r <;> first | rfl | exact absurd hr (by decide)
  have h127 : ((37 : ℕ) : ZMod 127) ^ n = 1 := by
    have h9' : ((37 : ℕ) : ZMod 127) ^ 9 = 1 := by decide
    rw [hn, hr0, add_zero, pow_mul, h9', one_pow]
  have h36 : ((37 : ℕ) : ZMod 127) - 1 ≠ 0 := by decide
  have : Fact (Nat.Prime 127) := ⟨by norm_num⟩
  have hg := geom_sum_mul ((37 : ℕ) : ZMod 127) n
  rw [h127, sub_self] at hg
  have hs : (∑ i ∈ Finset.range n, ((37 : ℕ) : ZMod 127) ^ i) = 0 :=
    (mul_eq_zero.1 hg).resolve_right h36
  have : ((∑ i ∈ Finset.range n, 37 ^ i : ℕ) : ZMod 127) = 0 := by
    push_cast
    simpa using hs
  exact (ZMod.natCast_eq_zero_iff _ _).1 this

end P9aacc79dAux

theorem solution (m d D p q4 sigma a b c e : Nat) (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 37) (hp_eq : p = 2 * D - 1) (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hddvd : d ∣ m ^ 2) (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) (hq4prime : q4.Prime) (hq4eq : q4 = 37) (haEven : Even a) (hbEven : Even b) (hcEven : Even c) (heEven : Even e) : False := by
  subst hD hq4eq
  have hp73 : p = 73 := by omega
  subst hp73
  have h73 : Nat.Prime 73 := by norm_num
  have hdvd : 73 ∣ 37 * sigma := ⟨m ^ 2, hrel⟩
  have hs : 73 ∣ sigma := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) hdvd)
  rw [hsigma] at hs
  rcases h73.dvd_mul.1 hs with h | h
  · rcases h73.dvd_mul.1 h with h | h
    · rcases h73.dvd_mul.1 h with h | h
      · exact P9aacc79dAux.three_ne a h
      · exact P9aacc79dAux.five_ne b h
    · exact P9aacc79dAux.twentynine_ne c h
  · have h127 := P9aacc79dAux.thirtyseven_127 _ h
    have hsig127 : 127 ∣ sigma := by
      rw [hsigma]; exact Dvd.dvd.mul_left h127 _
    have h1 : 127 ∣ 73 * m ^ 2 := by
      rw [← hrel]; exact Dvd.dvd.mul_left hsig127 _
    have h2 : 127 ∣ m ^ 2 := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h1
    have hpr : Nat.Prime 127 := by norm_num
    have h3 : 127 ∣ m := hpr.dvd_of_dvd_pow h2
    have hmem : 127 ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hpr, h3, hm0⟩
    rcases hsupport 127 hmem with h | h | h | h <;> norm_num at h
