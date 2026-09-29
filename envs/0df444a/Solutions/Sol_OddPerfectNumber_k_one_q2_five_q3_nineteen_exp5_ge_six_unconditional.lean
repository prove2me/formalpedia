-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T06:08:19.572657+00:00
-- url     : https://prove2.me/submissions/fe5ae20a-bab2-4e5a-adaa-17cc1fec8287

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_31_exp5_ge_six_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_ge_six_q4ne31_v2

theorem solution (p m d q4 sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, q4})
    (hsupport_m : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5)
    (h5even : Even ((m ^ 2).factorization 5))
    (hupper : sigma ≤ 2 * m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 5 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization q4 + 1), q4 ^ i)) :
    6 ≤ (m ^ 2).factorization 5 := by
  have hcases : q4 = 31 ∨ q4 ≠ 31 := by
    exact em (q4 = 31)
  rcases hcases with hq4eq | hq4eq
  · subst q4
    have hm0 : m ≠ 0 := by
      obtain ⟨u, hu⟩ := hm
      omega
    have hm2ne : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    have h3mem : 3 ∈ (m ^ 2).primeFactors := by
      rw [hsupport]
      simp
    have h19mem : 19 ∈ (m ^ 2).primeFactors := by
      rw [hsupport]
      simp
    have h31mem : 31 ∈ (m ^ 2).primeFactors := by
      rw [hsupport]
      simp
    have h3prime : (3 : Nat).Prime := by norm_num
    have h19prime : (19 : Nat).Prime := by norm_num
    have h31prime : (31 : Nat).Prime := by norm_num
    have h3pos : 0 < (m ^ 2).factorization 3 :=
      h3prime.factorization_pos_of_dvd hm2ne (Nat.dvd_of_mem_primeFactors h3mem)
    have h19pos : 0 < (m ^ 2).factorization 19 :=
      h19prime.factorization_pos_of_dvd hm2ne (Nat.dvd_of_mem_primeFactors h19mem)
    have h31pos : 0 < (m ^ 2).factorization 31 :=
      h31prime.factorization_pos_of_dvd hm2ne (Nat.dvd_of_mem_primeFactors h31mem)
    have h3fac : (m ^ 2).factorization 3 = 2 * m.factorization 3 := by
      simp [Nat.factorization_pow]
    have h19fac : (m ^ 2).factorization 19 = 2 * m.factorization 19 := by
      simp [Nat.factorization_pow]
    have h31fac : (m ^ 2).factorization 31 = 2 * m.factorization 31 := by
      simp [Nat.factorization_pow]
    have h3even : Even ((m ^ 2).factorization 3) := by
      rw [h3fac]
      exact even_two_mul _
    have h19even : Even ((m ^ 2).factorization 19) := by
      rw [h19fac]
      exact even_two_mul _
    have h31even : Even ((m ^ 2).factorization 31) := by
      rw [h31fac]
      exact even_two_mul _
    apply OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_31_exp5_ge_six_v3
      p m d sigma hp hp4 hm hpm hprod hsig
    · have hsupport31 := hsupport
      simpa using hsupport31
    · exact hsupport_m
    · exact hupper
    · simpa using hsigma
    · exact h3mem
    · exact h3pos
    · exact h3even
    · exact h19pos
    · exact h19even
    · exact h31pos
    · exact h31even
    · exact h5mem
    · exact h5pos
    · exact h5even
  · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_q4ne31_v2
      p m d q4 hp hp4 hm hpm hprod hsig hsupport_m hq4prime hq4gt
      h5mem h5pos h5even hq4eq
