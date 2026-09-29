-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_c_two_forces_q4_cases_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:44:35.10955+00:00
-- url     : https://prove2.me/submissions/21021a40-c43c-42d2-b4e2-d7eff665b0d3

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- c=2 means full exponent 4, sigma(17^4) = 88741, prime.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 17 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 17 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h17mem : 17 ∈ (m ^ 2).primeFactors)
    (h17exp : (m ^ 2).factorization 17 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    c ≠ 2 ∨ q4 = 88741 ∨ q4 = 44371 := by
  by_cases hc2 : c = 2
  ·
    have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
    have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    have h2c : 2 * c = 4 := by omega
    have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 17 hsq0 h17mem
    rw [h17exp, h2c] at hloc
    have hSeq : (∑ i ∈ Finset.range (4 + 1), 17 ^ i) = 88741 := by
      norm_num [Finset.sum_range_succ]
    rw [hSeq] at hloc
    have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
    have h88741dvd : 88741 ∣ ∑ x ∈ (m ^ 2).divisors, x := hloc
    have hprime : Nat.Prime 88741 := by norm_num
    have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
      p m d 3 5 17 q4 88741 hp hprime hm0 hsig hddvd h88741dvd hsupport
    rcases hcase with h | h | h | h | h
    · -- p = 88741: then D = 44371 (prime) divides m^2, forcing 44371 into support
      subst h
      have hhalf : ((88741 + 1) / 2) = 44371 := by norm_num
      have h44371 : m ^ 2 = 44371 * d := by
        calc m ^ 2 = ((88741 + 1) / 2) * d := hprod
          _ = 44371 * d := by rw [hhalf]
      have h44371dvd : (44371 : Nat) ∣ m ^ 2 := ⟨d, by omega⟩
      have h44371prime : Nat.Prime 44371 := by norm_num
      have h44371m : (44371 : Nat) ∣ m := h44371prime.dvd_of_dvd_pow h44371dvd
      have h44371mem : 44371 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨h44371prime, h44371m, hm0⟩
      have hdis := hsupport 44371 h44371mem
      rcases hdis with h3 | h5 | h17 | hq
      · omega
      · omega
      · omega
      · exact Or.inr (Or.inr hq.symm)
    · omega
    · omega
    · omega
    · exact Or.inr (Or.inl h.symm)
  · exact Or.inl hc2
