-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_divisor_small_absurd_half_floors_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T23:47:57.918646+00:00
-- url     : https://prove2.me/submissions/c65a5b0b-fc49-4ce6-86f1-89170ab3dc52

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_even_orders_mod_157_q3_twentythree
import Theorems.Thm_OddPerfectNumber_even_orders_mod_193_q3_twentythree

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hq4div : q4 ∣ D)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  have hDpos : 0 < D := hDodd.pos
  have hq4gt47 : 47 < q4 :=
    OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDpos hp_eq hq4prime hq4gt ha hb hc he
  have hcases :=
    OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
      D p q4 hDlt hDodd hp hp_eq hq4prime hq4gt hq4div
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · omega
  · omega
  · -- (D, q4) = (79, 79), so p = 157
    have hp157 : p = 157 := by omega
    have hP : Nat.Prime 157 := hp157 ▸ hp
    have h157 : 157 ∣ 79 * sigma := ⟨m ^ 2, by rw [hrel, hp157]⟩
    have hcop : Nat.Coprime 157 79 := by decide
    have hsdvd : 157 ∣ sigma := hcop.dvd_of_dvd_mul_left h157
    rw [hsigma] at hsdvd
    have e157 := OddPerfectNumber.even_orders_mod_157_q3_twentythree
    rcases (Nat.Prime.dvd_mul hP).mp hsdvd with h | h79
    · rcases (Nat.Prime.dvd_mul hP).mp h with h | h23
      · rcases (Nat.Prime.dvd_mul hP).mp h with h3 | h5
        · exact OddPerfectNumber.geom_sum_not_dvd_of_even_order e157.1 h3
        · exact OddPerfectNumber.geom_sum_not_dvd_of_even_order e157.2.1 h5
      · exact OddPerfectNumber.geom_sum_not_dvd_of_even_order e157.2.2.1 h23
    · exact OddPerfectNumber.geom_sum_not_dvd_of_even_order e157.2.2.2 h79
  · omega
  · -- (D, q4) = (97, 97), so p = 193
    have hp193 : p = 193 := by omega
    have hP : Nat.Prime 193 := hp193 ▸ hp
    have h193 : 193 ∣ 97 * sigma := ⟨m ^ 2, by rw [hrel, hp193]⟩
    have hcop : Nat.Coprime 193 97 := by decide
    have hsdvd : 193 ∣ sigma := hcop.dvd_of_dvd_mul_left h193
    rw [hsigma] at hsdvd
    have e193 := OddPerfectNumber.even_orders_mod_193_q3_twentythree
    rcases (Nat.Prime.dvd_mul hP).mp hsdvd with h | h97
    · rcases (Nat.Prime.dvd_mul hP).mp h with h | h23
      · rcases (Nat.Prime.dvd_mul hP).mp h with h3 | h5
        · exact OddPerfectNumber.geom_sum_not_dvd_of_even_order e193.1 h3
        · exact OddPerfectNumber.geom_sum_not_dvd_of_even_order e193.2.1 h5
      · exact OddPerfectNumber.geom_sum_not_dvd_of_even_order e193.2.2.1 h23
    · exact OddPerfectNumber.geom_sum_not_dvd_of_even_order e193.2.2.2 h97
