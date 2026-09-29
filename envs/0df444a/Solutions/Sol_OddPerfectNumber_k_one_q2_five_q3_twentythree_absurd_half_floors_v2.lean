-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_half_floors_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T14:35:21.830805+00:00
-- url     : https://prove2.me/submissions/77d498fc-70e9-460f-8e9b-8b89185d5238

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_even_orders_mod_157_q3_twentythree
import Theorems.Thm_OddPerfectNumber_even_orders_mod_193_q3_twentythree
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_small_D_lt_q4_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_absurd_half_floors_v1

-- EXPONENT CONVENTION: half exponents; full floors 8,6,4,2.
private theorem divisor_arm (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hq4div : q4 ∣ D)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  have hDpos : 0 < D := by have := hp.two_le; omega
  have hgt := OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
    m a b c e D p q4 sigma hfac hsigma hrel hDpos hp_eq hq4prime hq4gt ha hb hc he
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
    D p q4 hDlt hDodd hp hp_eq hq4prime hq4gt hq4div
  have htwo : (D = 79 ∧ q4 = 79) ∨ (D = 97 ∧ q4 = 97) := by omega
  rcases htwo with h79 | h97
  · rcases h79 with ⟨hD, hq⟩
    have hrel79 : 79 * sigma = 157 * m^2 := by simpa [hD, hp_eq] using hrel
    have hdiv : 157 ∣ sigma := by
      have hdvd : 157 ∣ 79 * sigma := ⟨m^2, hrel79⟩
      exact (by norm_num : Nat.Coprime 157 79).dvd_of_dvd_mul_left hdvd
    have heven := OddPerfectNumber.even_orders_mod_157_q3_twentythree
    have hnot (x t : Nat) (hx : Even (orderOf (x : ZMod 157))) :
        ¬ 157 ∣ ∑ i ∈ Finset.range (2*t+1), x^i :=
      OddPerfectNumber.geom_sum_not_dvd_of_even_order hx
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 157)).mp (by simpa [hsigma] using hdiv) with hr | hqsrc
    · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 157)).mp hr with hr' | h23
      · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 157)).mp hr' with h3 | h5
        · exact hnot 3 a heven.1 h3
        · exact hnot 5 b heven.2.1 h5
      · exact hnot 23 c heven.2.2.1 h23
    · exact hnot 79 e heven.2.2.2 (by simpa [hq] using hqsrc)
  · rcases h97 with ⟨hD, hq⟩
    have hrel97 : 97 * sigma = 193 * m^2 := by simpa [hD, hp_eq] using hrel
    have hdiv : 193 ∣ sigma := by
      have hdvd : 193 ∣ 97 * sigma := ⟨m^2, hrel97⟩
      exact (by norm_num : Nat.Coprime 193 97).dvd_of_dvd_mul_left hdvd
    have heven := OddPerfectNumber.even_orders_mod_193_q3_twentythree
    have hnot (x t : Nat) (hx : Even (orderOf (x : ZMod 193))) :
        ¬ 193 ∣ ∑ i ∈ Finset.range (2*t+1), x^i :=
      OddPerfectNumber.geom_sum_not_dvd_of_even_order hx
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 193)).mp (by simpa [hsigma] using hdiv) with hr | hqsrc
    · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 193)).mp hr with hr' | h23
      · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 193)).mp hr' with h3 | h5
        · exact hnot 3 a heven.1 h3
        · exact hnot 5 b heven.2.1 h5
      · exact hnot 23 c heven.2.2.1 h23
    · exact hnot 97 e heven.2.2.2 (by simpa [hq] using hqsrc)

-- All D-ranges and fourth-prime orderings, but floors are still premises.
theorem solution (m a b c e D p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) : False := by
  by_cases hsmall : D < 111
  · by_cases hlt : D < q4
    · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_small_D_lt_q4_absurd_half_floors_v1
        m a b c e D p q4 sigma hfac hsigma hrel hsmall hDodd hp hp_eq
        hq4prime hq4gt hlt hDsupport ha hb hc he
    · by_cases hdiv : q4 ∣ D
      · exact divisor_arm m a b c e D p q4 sigma hfac hsigma hrel hsmall hDodd
          hp hp_eq hq4prime hq4gt hdiv ha hb hc he
      · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_half_floors_v1
          m a b c e D p q4 sigma hfac hsigma hrel hsmall hDodd hp hp_eq
          hq4prime hq4gt hdiv hDsupport (by omega) ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_absurd_half_floors_v1
      m a b c e D p q4 sigma d hfac hsigma hrel (by omega) hp hp4 hp_eq
      hq4prime hq4gt hDsupport ha hb hc he hm0 hsig hddvd hsupport hglobal
