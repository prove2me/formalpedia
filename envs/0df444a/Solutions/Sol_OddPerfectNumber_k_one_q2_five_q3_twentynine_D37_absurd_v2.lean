-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D37_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T08:28:02.939049+00:00
-- url     : https://prove2.me/submissions/e1e57e25-a38f-4bf4-9354-a602ad6845f8

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_source_forces_37
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_source_length
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_local_127_of_length9
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_external_127_sigma_lift
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_external_127_absurd

theorem solution (m d D p q4 sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 37)
    (hp_eq : p = 2 * D - 1)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4eq : q4 = 37)
    (haEven : Even a) (hbEven : Even b) (hcEven : Even c) (heEven : Even e) :
    False := by
  subst D
  subst q4
  norm_num at hp_eq
  have hrel' : 37 * sigma = 73 * m ^ 2 := by
    simpa [hp_eq] using hrel
  have hmul : 73 ∣ 37 * sigma := by
    refine ⟨m ^ 2, ?_⟩
    exact hrel'
  have hdiv : 73 ∣ sigma := by
    exact (by norm_num : Nat.Coprime 73 37).dvd_of_dvd_mul_left hmul
  have hlocal := OddPerfectNumber.q2_five_q3_twentynine_D37_source_forces_37
    sigma a b c e hsigma hdiv haEven hbEven hcEven heEven
  have h9 := OddPerfectNumber.q2_five_q3_twentynine_D37_source_length e hlocal
  rcases h9 with ⟨k, hk⟩
  have hlen : 2 * e + 1 = 9 * k := by omega
  have h127local :=
    OddPerfectNumber.q2_five_q3_twentynine_D37_local_127_of_length9
      (2 * e + 1) k hlen
  have h127sigma :=
    OddPerfectNumber.q2_five_q3_twentynine_D37_external_127_sigma_lift
      sigma a b c e hsigma h127local
  have h127global : 127 ∣ ∑ x ∈ (m ^ 2).divisors, x := by
    simpa [hglobal] using h127sigma
  exact OddPerfectNumber.q2_five_q3_twentynine_D37_external_127_absurd
    p m d 37 hp hp4 hm0 hsig hddvd hsupport hq4prime rfl h127global
