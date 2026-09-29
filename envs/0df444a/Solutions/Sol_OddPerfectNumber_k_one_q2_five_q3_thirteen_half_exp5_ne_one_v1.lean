-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ne_one_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:21:49.402023+00:00
-- url     : https://prove2.me/submissions/3bef9b15-287a-4003-b2a6-3aa61c3d5af6

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_two_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_sum_ratio_mono_v1

theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hm : Odd m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    b ≠ 1 := by
  intro hb1
  subst hb1
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 5
    (pow_ne_zero 2 hm0) h5mem
  rw [h5exp] at hloc
  have v5 : ∑ i ∈ Finset.range (2 * 1 + 1), 5 ^ i = 31 := by
    norm_num [Finset.sum_range_succ]
  rw [v5] at hloc
  have h31 : Nat.Prime 31 := by norm_num
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [mul_comm]; exact hprod⟩
  have hrc := OddPerfectNumber.four_support_sigma_prime_restricted p m d 3 5 13 q4 31
    hp h31 hm0 hsig hddvd hloc hsupport
  obtain ⟨D, hDdef⟩ : ∃ D, D = (p + 1) / 2 := ⟨_, rfl⟩
  have h2 : 2 ≤ p := hp.two_le
  have hDpos : 0 < D := by omega
  have hp2 : p ≤ 2 * D := by omega
  have hsig2 : sigma = p * d := by rw [hglobal]; exact hsig
  have hprod2 : m ^ 2 = D * d := by rw [hDdef]; exact hprod
  have hrel : D * sigma = p * m ^ 2 := by rw [hsig2, hprod2]; ring
  have hDm : D ∣ m ^ 2 := ⟨d, hprod2⟩
  rcases hrc with h | h | h | h | h
  · -- 31 = p : D = 16, even, against m odd
    have hp31 : p = 31 := h.symm
    subst hp31
    have hD16 : D = 16 := by norm_num at hDdef; exact hDdef
    obtain ⟨t, ht⟩ := hDm
    rw [hD16] at ht
    obtain ⟨k, hk⟩ := hm
    rw [hk] at ht
    have hpar : (2 * k + 1) ^ 2 = 2 * (2 * k * k + 2 * k) + 1 := by ring
    rw [hpar] at ht
    omega
  · omega
  · omega
  · omega
  · -- 31 = q4 : minimum abundance exceeds 2
    subst h
    have hf5 : (5:Nat) ^ (2 * 1) = 25 := by norm_num
    rw [hf5] at hfac
    rw [v5] at hsigma
    have v31 : ∑ i ∈ Finset.range (2 + 1), 31 ^ i = 993 := by
      norm_num [Finset.sum_range_succ]
    have h2a : 2 ≤ 2 * a := by omega
    have h2c : 2 ≤ 2 * c := by omega
    have h2e : 2 ≤ 2 * e := by omega
    have r3 := OddPerfectNumber.geom_ratio_lower_three_ge_two_sharp (2 * a) h2a
    have r13 := OddPerfectNumber.geom_ratio_lower_thirteen_ge_two (2 * c) h2c
    have r31 := OddPerfectNumber.geom_sum_ratio_mono_v1 31 2 (2 * e) (by norm_num) h2e
    rw [v31] at r31
    set S3 := (∑ i ∈ Finset.range (2*a+1), 3^i) with hS3
    set S13 := (∑ i ∈ Finset.range (2*c+1), 13^i) with hS13
    set S31 := (∑ i ∈ Finset.range (2*e+1), 31^i) with hS31
    set A := 3^(2*a) * 13^(2*c) * 31^(2*e) with hA
    set C := 9 * 169 * 961 with hC
    set P := 13 * 183 * 993 with hP
    have hE2 : D * 31 * (S3 * S13 * S31) = p * 25 * A := by
      have h1 : sigma = (S3 * S13 * S31) * 31 := by rw [hsigma]; ring
      have h2f : m ^ 2 = A * 25 := by rw [hfac]; ring
      rw [h1, h2f] at hrel
      linarith [hrel]
    have e2 : P * A ≤ (S3 * S13 * S31) * C := by
      have h := Nat.mul_le_mul (Nat.mul_le_mul r3 r13) r31
      calc P * A = (13 * 3^(2*a)) * (183 * 13^(2*c)) * (993 * 31^(2*e)) := by
              rw [hP, hA]; ring
        _ ≤ (9 * S3) * (169 * S13) * (S31 * 961) := h
        _ = (S3 * S13 * S31) * C := by rw [hC]; ring
    have hApos : 0 < A := by positivity
    have hchain : (D * 31 * P) * A ≤ (p * 25 * C) * A := by
      calc (D * 31 * P) * A = (D * 31) * (P * A) := by ring
        _ ≤ (D * 31) * ((S3 * S13 * S31) * C) := Nat.mul_le_mul le_rfl e2
        _ = C * (D * 31 * (S3 * S13 * S31)) := by ring
        _ = C * (p * 25 * A) := by rw [hE2]
        _ = (p * 25 * C) * A := by ring
    have hKK : 2 * (25 * (9 * 169 * 961)) < 31 * (13 * 183 * 993) := by norm_num
    have hle2 : p * (25 * (9 * 169 * 961)) ≤ (2 * D) * (25 * (9 * 169 * 961)) :=
      Nat.mul_le_mul_right _ hp2
    have hlt2 : (2 * D) * (25 * (9 * 169 * 961)) < D * (31 * (13 * 183 * 993)) := by
      have h := mul_lt_mul_of_pos_left hKK hDpos
      calc (2 * D) * (25 * (9 * 169 * 961)) = D * (2 * (25 * (9 * 169 * 961))) := by ring
        _ < D * (31 * (13 * 183 * 993)) := h
    have hlt : p * (25 * (9 * 169 * 961)) < D * (31 * (13 * 183 * 993)) :=
      lt_of_le_of_lt hle2 hlt2
    have hle : D * 31 * P ≤ p * 25 * C :=
      Nat.le_of_mul_le_mul_right hchain hApos
    omega
