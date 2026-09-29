-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_le_139_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T07:40:59.287134+00:00
-- url     : https://prove2.me/submissions/5d96ebd5-472e-4e02-a7c6-2290bc0655c1

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_139_ratio_v1
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_q4_le_139_factor_cases_v5
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_factor_cases_absurd_v2

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 147 ≤ D)
    (hDhigh : D < 225) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4le : q4 ≤ 139)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  have hDdvd := OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
    m D p sigma hrel hp hp_eq
  have hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4 := by
    intro r hr hrD
    have hrm : r ∣ m ^ 2 := dvd_trans hrD hDdvd
    rw [hfac] at hrm
    rcases hr.dvd_mul.mp hrm with hrleft | hrq
    · rcases hr.dvd_mul.mp hrleft with hr35 | hr19
      · rcases hr.dvd_mul.mp hr35 with hr3 | hr5
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp
            (hr.dvd_of_dvd_pow hr3))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp
            (hr.dvd_of_dvd_pow hr5)))
      · exact Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp (hr.dvd_of_dvd_pow hr19))))
    · exact Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hr hq4prime).mp (hr.dvd_of_dvd_pow hrq))))
  have hcases := OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_le_139_factor_cases_v5
    m a b c e D p q4 sigma hfac hrel (by omega) hDhigh hp hp_eq
    hq4prime hq4gt hq4le hDsupport
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_factor_cases_absurd_v2
    m a b c e D p q4 sigma hfac hsigma hrel hcases ha hb hc he
