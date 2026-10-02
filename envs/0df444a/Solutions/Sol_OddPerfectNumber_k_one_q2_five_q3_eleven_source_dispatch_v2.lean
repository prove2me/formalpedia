-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_eleven_source_dispatch_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:16:21.005919+00:00
-- url     : https://prove2.me/submissions/9f966c96-0fed-4c0a-93e9-e024db6815f0

import Mathlib

set_option autoImplicit false

theorem p578d7e7e_geom (x n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (x + 1) ^ i) * x + 1 = (x + 1) ^ (n + 1) :=
  geom_sum_mul_add x (n + 1)

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
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  have h3 : (∑ i ∈ Finset.range (2 + 1), 3 ^ i) = 13 := by decide
  rw [h3] at hsigma
  have hpd : sigma = p * d := hglobal.trans hsig
  have h13 : 13 ∣ p * d := by
    rw [← hpd, hsigma]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl 13) _) _) _
  have hsupp : ∀ r : ℕ, r.Prime → r ∣ m → r = 3 ∨ r = 5 ∨ r = 11 ∨ r = q4 := by
    intro r hr hrm
    exact hsupport r (Nat.mem_primeFactors.mpr ⟨hr, hrm, hm0⟩)
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 13)).mp h13 with h | h
  · have hp13 : p = 13 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h).symm
    subst hp13
    have h7 : 7 ∣ m ^ 2 := by
      rw [hprod]
      exact Dvd.dvd.mul_right (by norm_num) _
    have h7m : 7 ∣ m := (by norm_num : Nat.Prime 7).dvd_of_dvd_pow h7
    have := hsupp 7 (by norm_num) h7m
    omega
  · have h13m2 : 13 ∣ m ^ 2 := by
      rw [hprod]
      exact Dvd.dvd.mul_left h _
    have h13m : 13 ∣ m := (by norm_num : Nat.Prime 13).dvd_of_dvd_pow h13m2
    have hq : q4 = 13 := by
      have := hsupp 13 (by norm_num) h13m
      omega
    subst hq
    -- abundance
    have hp2 : (p + 1) / 2 * 2 = p + 1 := by omega
    have h2m : 2 * m ^ 2 = (p + 1) * d := by
      calc 2 * m ^ 2 = ((p + 1) / 2 * 2) * d := by rw [hprod]; ring
        _ = (p + 1) * d := by rw [hp2]
    have hmpos : 0 < m ^ 2 := by positivity
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0, mul_zero] at hprod; omega
      · exact h0
    have hlt : sigma < 2 * m ^ 2 := by
      rw [hpd, h2m, add_mul, one_mul]; omega
    set A := 5 ^ b with hA
    set B := 11 ^ c with hB
    set C := 13 ^ e with hC
    set S5 := ∑ i ∈ Finset.range (b + 1), 5 ^ i with hS5
    set S11 := ∑ i ∈ Finset.range (c + 1), 11 ^ i with hS11
    set S13 := ∑ i ∈ Finset.range (e + 1), 13 ^ i with hS13
    have g5 : S5 * 4 + 1 = 5 * A := by
      have := p578d7e7e_geom 4 b
      rw [hS5, hA, ← pow_succ']
      simpa using this
    have g11 : S11 * 10 + 1 = 11 * B := by
      have := p578d7e7e_geom 10 c
      rw [hS11, hB, ← pow_succ']
      simpa using this
    have g13 : S13 * 12 + 1 = 13 * C := by
      have := p578d7e7e_geom 12 e
      rw [hS13, hC, ← pow_succ']
      simpa using this
    have hA25 : 25 ≤ A := by
      rw [hA]; calc (25:ℕ) = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    have hB121 : 121 ≤ B := by
      rw [hB]; calc (121:ℕ) = 11 ^ 2 := by norm_num
        _ ≤ 11 ^ c := Nat.pow_le_pow_right (by norm_num) hc
    have hC169 : 169 ≤ C := by
      rw [hC]; calc (169:ℕ) = 13 ^ 2 := by norm_num
        _ ≤ 13 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have i5 : 31 * A ≤ 25 * S5 := by omega
    have i11 : 133 * B ≤ 121 * S11 := by omega
    have i13 : 183 * C ≤ 169 * S13 := by omega
    have j1 : (31 * A) * (133 * B) ≤ (25 * S5) * (121 * S11) := Nat.mul_le_mul i5 i11
    have j2 : (31 * A) * (133 * B) * (183 * C) ≤ (25 * S5) * (121 * S11) * (169 * S13) :=
      Nat.mul_le_mul j1 i13
    have hpos : 0 < A * B * C := by positivity
    have e1 : (31 * A) * (133 * B) * (183 * C) = 754509 * (A * B * C) := by ring
    have e2 : (25 * S5) * (121 * S11) * (169 * S13) = 511225 * (S5 * S11 * S13) := by ring
    have e3 : sigma = 13 * (S5 * S11 * S13) := by rw [hsigma]; ring
    have e4 : m ^ 2 = 9 * (A * B * C) := by rw [hfac]; ring
    rw [e1, e2] at j2
    rw [e3, e4] at hlt
    omega
