-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_eleven_source_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:57:09.282057+00:00
-- url     : https://prove2.me/submissions/82bf463c-8201-4153-83b2-66c2059f657d

import Mathlib

set_option autoImplicit false

namespace OddPerfectNumber

theorem ab5faf4c_geom_lower (q n : Nat) :
    (1 + q + q ^ 2) * q ^ n ≤ ∑ i ∈ Finset.range (n + 3), q ^ i := by
  have h : ∑ i ∈ Finset.range (n + 3), q ^ i
      = (∑ i ∈ Finset.range n, q ^ i) + (1 + q + q ^ 2) * q ^ n := by
    rw [show n + 3 = n + 1 + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring
  rw [h]
  exact Nat.le_add_left _ _

theorem ab5faf4c_seven_not_dvd (b c e q4 : Nat) (hq4prime : q4.Prime) (hq4gt : 11 < q4) :
    ¬ 7 ∣ 3 ^ 2 * 5 ^ b * 11 ^ c * q4 ^ e := by
  have h7 : Nat.Prime 7 := by norm_num
  intro h
  rcases (Nat.Prime.dvd_mul h7).1 h with h | h
  · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
    · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
      · have := Nat.Prime.dvd_of_dvd_pow h7 h; norm_num at this
      · have := Nat.Prime.dvd_of_dvd_pow h7 h; norm_num at this
    · have := Nat.Prime.dvd_of_dvd_pow h7 h; norm_num at this
  · have := Nat.Prime.dvd_of_dvd_pow h7 h
    have := (Nat.prime_dvd_prime_iff_eq h7 hq4prime).1 this
    omega

theorem ab5faf4c_q4_eq (b c e q4 : Nat) (hq4prime : q4.Prime)
    (h : 13 ∣ 3 ^ 2 * 5 ^ b * 11 ^ c * q4 ^ e) : q4 = 13 := by
  have h13 : Nat.Prime 13 := by norm_num
  rcases (Nat.Prime.dvd_mul h13).1 h with h | h
  · rcases (Nat.Prime.dvd_mul h13).1 h with h | h
    · rcases (Nat.Prime.dvd_mul h13).1 h with h | h
      · have := Nat.Prime.dvd_of_dvd_pow h13 h; norm_num at this
      · have := Nat.Prime.dvd_of_dvd_pow h13 h; norm_num at this
    · have := Nat.Prime.dvd_of_dvd_pow h13 h; norm_num at this
  · have := Nat.Prime.dvd_of_dvd_pow h13 h
    exact ((Nat.prime_dvd_prime_iff_eq h13 hq4prime).1 this).symm

theorem ab5faf4c_main
    (m b c e p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ 2 * 5 ^ b * 11 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 11 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 11 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  have hS3 : (∑ i ∈ Finset.range (2 + 1), 3 ^ i) = 13 := by decide
  set S5 := ∑ i ∈ Finset.range (b + 1), 5 ^ i with hS5
  set S11 := ∑ i ∈ Finset.range (c + 1), 11 ^ i with hS11
  set Sq := ∑ i ∈ Finset.range (e + 1), q4 ^ i with hSq
  rw [hS3] at hsigma
  have hP : 13 * S5 * S11 * Sq = p * d := by rw [← hsigma, hglobal, hsig]
  obtain ⟨k, hk⟩ : ∃ k, p + 1 = 2 * k := ⟨(p + 1) / 2, by omega⟩
  have hkd : (p + 1) / 2 = k := by omega
  rw [hkd] at hprod
  -- key identity: sigma * (p+1) = 2 p (m ^ 2)
  have hkey : (13 * S5 * S11 * Sq) * (p + 1) = 2 * p * (m ^ 2) := by
    rw [hP, hk, hprod]; try ring
  by_cases hp13 : p = 13
  · subst hp13
    have h7 : 7 ∣ 13 * (m ^ 2) := by
      refine ⟨13 * S5 * S11 * Sq, ?_⟩
      have : (13 * S5 * S11 * Sq) * 14 = 26 * (m ^ 2) := by rw [hkey]; try ring
      omega
    have h7' : 7 ∣ (m ^ 2) := by
      have := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 7 13) h7)
      exact this
    rw [hfac] at h7'
    exact ab5faf4c_seven_not_dvd b c e q4 hq4prime hq4gt h7'
  · have h13pd : 13 ∣ p * d := ⟨S5 * S11 * Sq, by rw [← hP]; ring⟩
    have h13 : Nat.Prime 13 := by norm_num
    rcases (Nat.Prime.dvd_mul h13).1 h13pd with h | h
    · exact hp13 ((Nat.prime_dvd_prime_iff_eq h13 hp).1 h).symm
    · have h13M : 13 ∣ (m ^ 2) := by rw [hprod]; exact Dvd.dvd.mul_left h k
      rw [hfac] at h13M
      have hq : q4 = 13 := ab5faf4c_q4_eq b c e q4 hq4prime h13M
      subst hq
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
      have l5 := ab5faf4c_geom_lower 5 b'
      have l11 := ab5faf4c_geom_lower 11 c'
      have l13 := ab5faf4c_geom_lower 13 e'
      rw [show b' + 3 = b' + 2 + 1 by omega] at l5
      rw [show c' + 3 = c' + 2 + 1 by omega] at l11
      rw [show e' + 3 = e' + 2 + 1 by omega] at l13
      rw [← hS5] at l5
      rw [← hS11] at l11
      rw [← hSq] at l13
      norm_num at l5 l11 l13
      -- P < 2 (m ^ 2)
      have hlt : 13 * S5 * S11 * Sq < 2 * (m ^ 2) := by
        have hp0 : 0 < p := hp.pos
        by_contra hcon
        push Not at hcon
        have h0 : 2 * (m ^ 2) * (p + 1) ≤ 13 * S5 * S11 * Sq * (p + 1) :=
          Nat.mul_le_mul_right _ hcon
        have hm2 : 0 < m ^ 2 := by rw [hfac]; positivity
        rw [hkey] at h0
        nlinarith
      rw [hfac] at hlt
      have X5 : 0 < 5 ^ b' := by positivity
      have X11 : 0 < 11 ^ c' := by positivity
      have X13 : 0 < 13 ^ e' := by positivity
      have hge : 13 * (31 * 5 ^ b') * (133 * 11 ^ c') * (183 * 13 ^ e')
          ≤ 13 * S5 * S11 * Sq := by
        apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl l5) l11) l13
      have hX : 0 < 5 ^ b' * 11 ^ c' * 13 ^ e' := by positivity
      have e1 : 2 * (3 ^ 2 * 5 ^ (b' + 2) * 11 ^ (c' + 2) * 13 ^ (e' + 2))
          = 9202050 * (5 ^ b' * 11 ^ c' * 13 ^ e') := by ring
      have e2 : 13 * (31 * 5 ^ b') * (133 * 11 ^ c') * (183 * 13 ^ e')
          = 9808617 * (5 ^ b' * 11 ^ c' * 13 ^ e') := by ring
      omega

end OddPerfectNumber

/-- top-level solution -/
theorem solution
    (m b c e p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ 2 * 5 ^ b * 11 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 11 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 11 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  exact OddPerfectNumber.ab5faf4c_main m b c e p q4 sigma d hfac hsigma
    hglobal hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt h3mem h3exp hb hc he
