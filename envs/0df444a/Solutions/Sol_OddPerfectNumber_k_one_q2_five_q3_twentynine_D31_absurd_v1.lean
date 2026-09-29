-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D31_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T12:14:34.909252+00:00
-- url     : https://prove2.me/submissions/7c6cb8d2-bafa-4f55-a50a-ddb47b4d012a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_even_orders_mod_61_q3_twentynine
import Theorems.Thm_OddPerfectNumber_even_order_31_mod_61

theorem solution (m a b c e D p q4 sigma : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 31)
    (hp_eq : p = 2 * D - 1)
    (hp : p.Prime)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (hq4prime : q4.Prime)
    (haEven : Even a) (hbEven : Even b) (hcEven : Even c) (heEven : Even e) :
    False := by
  have hq4eq : q4 = 31 := by
    rcases hDsupport 31 (by norm_num) (by simpa [hD]) with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact h.symm
  subst q4
  have hrel' : 31 * sigma = 61 * m ^ 2 := by
    simpa [hD, hp_eq] using hrel
  have hmul : 61 ∣ 31 * sigma := by
    refine ⟨m ^ 2, ?_⟩
    exact hrel'
  have hdiv : 61 ∣ sigma :=
    (by norm_num : Nat.Coprime 61 31).dvd_of_dvd_mul_left hmul
  rw [hsigma] at hdiv
  have hp61 : Nat.Prime 61 := by norm_num
  rcases hp61.dvd_mul.mp hdiv with hleft | h31
  · rcases hp61.dvd_mul.mp hleft with hleft | h29
    · rcases hp61.dvd_mul.mp hleft with h3 | h5
      · exact (OddPerfectNumber.geom_sum_not_dvd_of_even_order
          (OddPerfectNumber.even_orders_mod_61_q3_twentynine.1)) h3
      · exact (OddPerfectNumber.geom_sum_not_dvd_of_even_order
          (OddPerfectNumber.even_orders_mod_61_q3_twentynine.2.1)) h5
    · exact (OddPerfectNumber.geom_sum_not_dvd_of_even_order
        (OddPerfectNumber.even_orders_mod_61_q3_twentynine.2.2)) h29
  · exact (OddPerfectNumber.geom_sum_not_dvd_of_even_order
      OddPerfectNumber.even_order_31_mod_61) h31
