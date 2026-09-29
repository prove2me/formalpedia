-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_residual_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T01:49:29.873526+00:00
-- url     : https://prove2.me/submissions/67984498-b184-415b-9f7c-542eb2b1b578

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_q4_53_no_five_source_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_q4_59_no_five_source_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_q4_67_no_five_source_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_q4_79_no_five_source_v2

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hb : 8 ≤ b)
    (hcases :
      (D = 79 ∧ p = 157 ∧ q4 = 79) ∨
      (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
      (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
      (D = 201 ∧ p = 401 ∧ q4 = 67)) :
    False := by
  have h5pow : 5 ∣ 5 ^ (2*b) := dvd_pow_self 5 (by omega)
  have h5m : 5 ∣ m ^ 2 := by
    rw [hfac]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_right
          (dvd_mul_of_dvd_right h5pow (3 ^ (2*a)))
          (13 ^ (2*c)))
        (q4 ^ (2*e)))
  have hfive_of_not_dvd : ¬ 5 ∣ D → 5 ∣ sigma := by
    intro hD
    have hpm : 5 ∣ p * m ^ 2 := dvd_mul_of_dvd_right h5m p
    have hDsig : 5 ∣ D * sigma := by
      rw [hrel]
      exact hpm
    rcases ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp hDsig) with h | h
    · exact False.elim (hD h)
    · exact h
  rcases hcases with h | h | h | h
  · rcases h with ⟨rfl, rfl, rfl⟩
    have hfive : 5 ∣ sigma := hfive_of_not_dvd (by norm_num)
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_q4_79_no_five_source_v2
      sigma a b c e hsigma hfive
  · rcases h with ⟨rfl, rfl, rfl⟩
    have hfive : 5 ∣ sigma := hfive_of_not_dvd (by norm_num)
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_q4_53_no_five_source_v2
      sigma a b c e hsigma hfive
  · rcases h with ⟨rfl, rfl, rfl⟩
    have hfive : 5 ∣ sigma := hfive_of_not_dvd (by norm_num)
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_q4_59_no_five_source_v2
      sigma a b c e hsigma hfive
  · rcases h with ⟨rfl, rfl, rfl⟩
    have hfive : 5 ∣ sigma := hfive_of_not_dvd (by norm_num)
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_q4_67_no_five_source_v2
      sigma a b c e hsigma hfive
