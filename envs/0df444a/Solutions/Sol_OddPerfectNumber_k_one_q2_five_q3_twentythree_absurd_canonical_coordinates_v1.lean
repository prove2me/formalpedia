-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_canonical_coordinates_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T17:09:50.026265+00:00
-- url     : https://prove2.me/submissions/bb0ef3a2-6645-4204-a6df-61659ff374a5

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v4
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_order_three_mod_five_eq_four
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_half_exp23_ge2_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_absurd_half_floors_v2

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents throughout.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h23mem : 23 ∈ (m ^ 2).primeFactors)
    (h23exp : (m ^ 2).factorization 23 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) : False := by
  have hm0 : m ≠ 0 := by rcases hm with ⟨u, hu⟩; omega
  have hmpos : 0 < m^2 := Nat.pos_of_ne_zero (pow_ne_zero 2 hm0)
  have hddvd : d ∣ m^2 := by
    refine ⟨(p+1)/2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  have hpd : sigma = p*d := hglobal.trans hsig
  have hDpos : 0 < (p+1)/2 := by have := hp.two_le; omega
  have hrel : ((p+1)/2)*sigma = p*m^2 := by rw [hpd, hprod]; ring
  have hDodd : Odd ((p+1)/2) := by refine ⟨p/4, ?_⟩; omega
  have hpeq : p = 2*((p+1)/2)-1 := by omega
  have hDdvd : (p+1)/2 ∣ m^2 := ⟨d, hprod⟩
  have hDsupport (r : Nat) (hr : r.Prime) (hrD : r ∣ (p+1)/2) :
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4 := by
    exact hsupport r (Nat.mem_primeFactors.mpr
      ⟨hr, hr.dvd_of_dvd_pow (hrD.trans hDdvd), hm0⟩)
  have hrole (q t r : Nat) (hq : q ∈ (m^2).primeFactors)
      (hx : (m^2).factorization q = t) (hr : r.Prime)
      (hd : r ∣ ∑ i ∈ Finset.range (t+1), q^i) :
      r = p ∨ r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4 := by
    have hl := OddPerfectNumber.local_sigma_factor_dvd_global
      (m^2) q (pow_ne_zero 2 hm0) hq
    rw [hx] at hl
    exact OddPerfectNumber.four_support_sigma_prime_restricted
      p m d 3 5 23 q4 r hp hr hm0 hsig hddvd (hd.trans hl) hsupport
  have ha1 : a ≠ 1 := by
    intro h
    have hx : (m^2).factorization 3 = 2 := by simpa [h] using h3exp
    have hr := hrole 3 2 13 h3mem hx (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    have hp13 : p = 13 := by omega
    have hd7 : 7 ∣ (p+1)/2 := by norm_num [hp13]
    have hs := hDsupport 7 (by norm_num) hd7
    omega
  have ha2 : a ≠ 2 := by
    intro h
    have hx : (m^2).factorization 3 = 4 := by simpa [h] using h3exp
    have hr := hrole 3 4 11 h3mem hx (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    have hp11 : p = 11 := by omega
    norm_num [hp11] at hp4
  have ha3 : 3 ≤ a := by omega
  have hupper : sigma ≤ 2*m^2 := by
    have hhalf : p ≤ 2*((p+1)/2) := by omega
    calc
      sigma = p*d := hpd
      _ ≤ (2*((p+1)/2))*d := Nat.mul_le_mul_right d hhalf
      _ = 2*m^2 := by rw [hprod]; ring
  have hb1 : b ≠ 1 := by
    intro h
    have hx : (m^2).factorization 5 = 2 := by simpa [h] using h5exp
    have hr := hrole 5 2 31 h5mem hx (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    have hq31 : q4 = 31 := by
      rcases hr with hrp | hr3 | hr5 | hr23 | hrq
      · have hp31 : p = 31 := hrp.symm
        norm_num [hp31] at hp4
      · norm_num at hr3
      · norm_num at hr5
      · norm_num at hr23
      · exact hrq.symm
    have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_six (2*a) (by omega)
    have h5 := OddPerfectNumber.geom_ratio_lower_three_terms_exact_v4 5 b (by omega)
    have h23 := OddPerfectNumber.geom_ratio_lower_three_terms_exact_v4 23 c (by omega)
    have h31 := OddPerfectNumber.geom_ratio_lower_three_terms_exact_v4 31 e (by omega)
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) (Nat.mul_le_mul h23 h31)
    have hcross : (1093*31*553*993)*m^2 ≤ (729*25*529*961)*sigma := by
      rw [hfac, hsigma, hq31]
      convert hmul using 1 <;> ring
    omega
  have hb2 : b ≠ 2 := by
    intro h
    have hx : (m^2).factorization 5 = 4 := by simpa [h] using h5exp
    have hr := hrole 5 4 11 h5mem hx (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    have hp11 : p = 11 := by omega
    norm_num [hp11] at hp4
  have hb3 : 3 ≤ b := by omega
  have ha4 : 4 ≤ a := by
    by_contra hn
    have haeq : a = 3 := by omega
    have hx : (m^2).factorization 3 = 6 := by simpa [haeq] using h3exp
    have hr := hrole 3 6 1093 h3mem hx (by norm_num)
      (by norm_num [Finset.sum_range_succ])
    have hroles : p = 1093 ∨ q4 = 1093 := by omega
    have hqge : 547 ≤ q4 := by
      rcases hroles with hp1093 | hq1093
      · have hd547 : 547 ∣ (p+1)/2 := by norm_num [hp1093]
        have hs := hDsupport 547 (by norm_num) hd547
        omega
      · omega
    have u3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
      (by norm_num) (by norm_num) (by norm_num)
    have u5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
      (by norm_num) (by norm_num) (by norm_num)
    have u23 := OddPerfectNumber.geom_sum_cross_lt_of_le 23 23 (2*c)
      (by norm_num) (by norm_num) (by norm_num)
    have uq := OddPerfectNumber.geom_sum_cross_lt_of_le 547 q4 (2*e)
      (by norm_num) hqge hq4prime
    have hu := Nat.mul_lt_mul_of_lt_of_lt
      (Nat.mul_lt_mul_of_lt_of_lt u3 u5) (Nat.mul_lt_mul_of_lt_of_lt u23 uq)
    have hbound : 96096*sigma < 188715*m^2 := by
      rw [hfac, hsigma]
      convert hu using 1 <;> ring
    have hmul : (96096*p)*m^2 < (188715*((p+1)/2))*m^2 := by
      calc
        (96096*p)*m^2 = 96096*(p*m^2) := by ring
        _ = 96096*(((p+1)/2)*sigma) := by rw [hrel]
        _ = ((p+1)/2)*(96096*sigma) := by ring
        _ < ((p+1)/2)*(188715*m^2) := (Nat.mul_lt_mul_left hDpos).2 hbound
        _ = (188715*((p+1)/2))*m^2 := by ring
    have hcoef := Nat.lt_of_mul_lt_mul_right hmul
    have hDsmall : (p+1)/2 < 185 := by omega
    rcases hroles with hp1093 | hq1093
    · omega
    · have h5pow : 5^6 ∣ 5^(2*b) := pow_dvd_pow 5 (by omega)
      have h5fac : 5^(2*b) ∣ m^2 := by
        rw [hfac]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
      have h5sig := OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
        p m d sigma hp hprod hpd hDsmall (h5pow.trans h5fac)
      have hnot (x t : Nat) (hx3 : (x : ZMod 5) = (3 : ZMod 5)) :
          ¬ 5 ∣ ∑ i ∈ Finset.range (2*t+1), x^i := by
        apply OddPerfectNumber.geom_sum_not_dvd_of_order_certificate
        rw [hx3, OddPerfectNumber.order_three_mod_five_eq_four]
        omega
      have hno3 := hnot 3 a rfl
      have hno23 := hnot 23 c (by decide)
      have hno1093 := hnot 1093 e (by decide)
      have hno5 := OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow 5 (2*b) (by norm_num)
      rw [hsigma, hq1093] at h5sig
      rcases (by norm_num : Nat.Prime 5).dvd_mul.mp h5sig with hl | hq
      · rcases (by norm_num : Nat.Prime 5).dvd_mul.mp hl with hl' | h23
        · rcases (by norm_num : Nat.Prime 5).dvd_mul.mp hl' with h3 | h5
          · exact hno3 h3
          · exact hno5 h5
        · exact hno23 h23
      · exact hno1093 hq
  have hc2 := OddPerfectNumber.k_one_q2_five_q3_twentythree_half_exp23_ge2_v1
    p m d q4 c hp hp4 hm hprod hsig hsupport hq4gt h23mem h23exp hc
  exact OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_half_floors_v2
    m a b c e ((p+1)/2) p q4 sigma d hfac hsigma hrel hDodd hp hp4 hpeq
    hq4prime hq4gt hDsupport ha4 hb3 hc2 (by omega) hm0 hsig hddvd hsupport hglobal
