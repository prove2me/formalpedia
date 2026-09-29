-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D37_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T03:04:15.055267+00:00
-- url     : https://prove2.me/submissions/b3a84edf-5c85-4b9d-917d-4e4c28784169

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_even_orders_mod_73_q3_twentynine
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_source_length
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_local_127_of_length9
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_external_127_sigma_lift
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_external_127_absurd

theorem solution (m d D p q4 sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 37)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (hq4prime : q4.Prime) : False := by
  subst D
  norm_num at hp_eq
  subst p
  have h37prime : Nat.Prime 37 := by norm_num
  have h73prime : Nat.Prime 73 := by norm_num
  have hq4eq : q4 = 37 := by
    have hcase := hDsupport 37 h37prime (by exact dvd_refl 37)
    rcases hcase with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact h.symm
  subst q4
  have h73left : 73 ∣ 37 * sigma := by
    rw [hrel]
    simpa [Nat.mul_comm] using (dvd_mul_left 73 (m ^ 2))
  have h73sigma : 73 ∣ sigma := by
    rcases h73prime.dvd_mul.mp h73left with hbad | hs
    · norm_num at hbad
    · exact hs
  rw [hsigma] at h73sigma
  have h3 : ¬ 73 ∣ (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order
      (OddPerfectNumber.even_orders_mod_73_q3_twentynine.1)
  have h5 : ¬ 73 ∣ (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order
      (OddPerfectNumber.even_orders_mod_73_q3_twentynine.2.1)
  have h29 : ¬ 73 ∣ (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) :=
    OddPerfectNumber.geom_sum_not_dvd_of_even_order
      (OddPerfectNumber.even_orders_mod_73_q3_twentynine.2.2)
  have hlocal : 73 ∣ (∑ i ∈ Finset.range (2*e + 1), 37 ^ i) := by
    rcases h73prime.dvd_mul.mp h73sigma with hleft | hlocal
    · rcases h73prime.dvd_mul.mp hleft with hleft2 | h29s
      · rcases h73prime.dvd_mul.mp hleft2 with h3s | h5s
        · exact False.elim (h3 h3s)
        · exact False.elim (h5 h5s)
      · exact False.elim (h29 h29s)
    · exact hlocal
  have hlen : 9 ∣ 2*e + 1 :=
    OddPerfectNumber.q2_five_q3_twentynine_D37_source_length e hlocal
  obtain ⟨k, hk⟩ := hlen
  have h127local : 127 ∣ (∑ i ∈ Finset.range (2*e + 1), 37 ^ i) := by
    exact OddPerfectNumber.q2_five_q3_twentynine_D37_local_127_of_length9
      (2*e + 1) k hk
  have h127sigma : 127 ∣ sigma :=
    OddPerfectNumber.q2_five_q3_twentynine_D37_external_127_sigma_lift
      sigma a b c e hsigma h127local
  have h127div : 127 ∣ ∑ x ∈ (m ^ 2).divisors, x := by
    rw [← hglobal]
    exact h127sigma
  exact OddPerfectNumber.q2_five_q3_twentynine_D37_external_127_absurd
    73 m d 37 hp hp4 hm0 hsig hddvd hsupport hq4prime rfl h127div
