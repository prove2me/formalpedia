-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_nondivisor_half_floors_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T12:03:55.383871+00:00
-- url     : https://prove2.me/submissions/1c336ac5-05d4-4951-805b-0a4981d2368e

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_dvd_square_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_factor_support_form_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_D_le_481_v1
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v4

private theorem support_cases (D p i j k : Nat)
    (hform : D = 3^i * 5^j * 23^k) (hlo : 111 ≤ D) (hhi : D ≤ 481)
    (hp : p.Prime) (hp_eq : p = 2*D-1) :
    D = 115 ∨ D = 135 ∨ D = 225 ∨ D = 405 := by
  have hi : i ≤ 5 := by
    by_contra hn
    have hg : 6 ≤ i := by omega
    have hb : 729 ≤ 3^i := by
      calc 729 = 3^6 := by norm_num
           _ ≤ 3^i := Nat.pow_le_pow_right (by norm_num) hg
    have ht : 3^i ≤ D := by
      rw [hform]
      have ht := Nat.le_mul_of_pos_right (3^i) (by positivity : 0 < 5^j * 23^k)
      simpa only [Nat.mul_assoc] using ht
    omega
  have hj : j ≤ 3 := by
    by_contra hn
    have hg : 4 ≤ j := by omega
    have hb : 625 ≤ 5^j := by
      calc 625 = 5^4 := by norm_num
           _ ≤ 5^j := Nat.pow_le_pow_right (by norm_num) hg
    have ht : 5^j ≤ D := by
      rw [hform]
      have ht := Nat.le_mul_of_pos_right (5^j) (by positivity : 0 < 3^i * 23^k)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht
    omega
  have hk : k ≤ 1 := by
    by_contra hn
    have hg : 2 ≤ k := by omega
    have hb : 529 ≤ 23^k := by
      calc 529 = 23^2 := by norm_num
           _ ≤ 23^k := Nat.pow_le_pow_right (by norm_num) hg
    have ht : 23^k ≤ D := by
      rw [hform]
      have ht := Nat.le_mul_of_pos_right (23^k) (by positivity : 0 < 3^i * 5^j)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht
    omega
  interval_cases i <;> interval_cases j <;> interval_cases k
  all_goals norm_num at hform
  all_goals rw [hform] at hp_eq
  all_goals norm_num at hp_eq
  all_goals rw [hp_eq] at hp
  all_goals norm_num at hp
  all_goals omega

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full floors are 8,6,4,2.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2*D-1) (hq4prime : q4.Prime)
    (hqcases : q4 = 53 ∨ q4 = 59 ∨ q4 = 61) (hnot : ¬ q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  have hqge : 53 ≤ q4 := by rcases hqcases with h | h | h <;> omega
  have hDhi := OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_D_le_481_v1
    m a b c e D p q4 sigma hfac hsigma hrel (by omega) hp_eq hq4prime hqge
  have hDdvd := OddPerfectNumber.k_one_q2_five_q3_twentythree_D_dvd_square_v1
    m D p sigma hrel hp hp_eq
  obtain ⟨i, j, k, l, hform, _, _, _, _⟩ :=
    OddPerfectNumber.k_one_q2_five_q3_twentythree_D_factor_support_form_v1
      m a b c e D q4 hfac hDdvd (by omega) hq4prime (by omega) hDsupport
  have hl : l = 0 := by
    cases l with
    | zero => rfl
    | succ l =>
      exfalso
      apply hnot
      rw [hform, pow_succ]
      exact ⟨3^i * 5^j * 23^k * q4^l, by ring⟩
  rw [hl] at hform
  simp only [pow_zero, mul_one] at hform
  have hDcases := support_cases D p i j k hform hDlow hDhi hp hp_eq
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
    (by norm_num) (by norm_num) (by norm_num)
  have hu23 := OddPerfectNumber.geom_sum_cross_lt_of_le 23 23 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e)
    (by omega) (by rfl) hq4prime
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu5) (Nat.mul_lt_mul_of_lt_of_lt hu23 huq)
  have hupper : 176*(q4-1)*sigma < 345*q4*m^2 := by
    calc
      176*(q4-1)*sigma =
        ((2*(∑ i ∈ Finset.range (2*a+1), 3^i)) *
         (4*(∑ i ∈ Finset.range (2*b+1), 5^i))) *
        ((22*(∑ i ∈ Finset.range (2*c+1), 23^i)) *
         ((q4-1)*(∑ i ∈ Finset.range (2*e+1), q4^i))) := by rw [hsigma]; ring
      _ < ((3*3^(2*a))*(5*5^(2*b))) * ((23*23^(2*c))*(q4*q4^(2*e))) := hu
      _ = 345*q4*m^2 := by rw [hfac]; ring
  have huppercoef : 176*(q4-1)*p < 345*q4*D := by
    apply Nat.lt_of_mul_lt_mul_right (a := m^2)
    calc
      (176*(q4-1)*p)*m^2 = D*(176*(q4-1)*sigma) := by
        calc
          _ = (176*(q4-1))*(p*m^2) := by ring
          _ = (176*(q4-1))*(D*sigma) := by rw [hrel]
          _ = _ := by ring
      _ < D*(345*q4*m^2) := (Nat.mul_lt_mul_left (by omega : 0 < D)).2 hupper
      _ = (345*q4*D)*m^2 := by ring
  have hl3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have hl5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hgeom23 := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
  rw [pow_succ] at hgeom23
  have hpow23 : 23 ^ 4 ≤ 23 ^ (2*c) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
  have hl23 : 292561 * 23 ^ (2*c) ≤
      279841 * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) := by omega
  have hlq := OddPerfectNumber.geom_ratio_lower_three_terms_exact_v4 q4 e he
  have hlower := Nat.mul_le_mul (Nat.mul_le_mul hl3 hl5) (Nat.mul_le_mul hl23 hlq)
  have hlowercross : (9841*19531*292561*(q4^2+q4+1))*m^2 ≤
      (6561*15625*279841*q4^2)*sigma := by
    calc
      _ = ((9841*3^(2*a))*(19531*5^(2*b))) *
          ((292561*23^(2*c))*((q4^2+q4+1)*q4^(2*e))) := by rw [hfac]; ring
      _ ≤ ((6561*(∑ i ∈ Finset.range (2*a+1), 3^i))*
           (15625*(∑ i ∈ Finset.range (2*b+1), 5^i))) *
          ((279841*(∑ i ∈ Finset.range (2*c+1), 23^i))*
           (q4^2*(∑ i ∈ Finset.range (2*e+1), q4^i))) := hlower
      _ = _ := by rw [hsigma]; ring
  have hlowercoef : (9841*19531*292561*(q4^2+q4+1))*D ≤
      (6561*15625*279841*q4^2)*p := by
    apply Nat.le_of_mul_le_mul_right (c := m^2) _ hmpos
    calc
      ((9841*19531*292561*(q4^2+q4+1))*D)*m^2 =
          D*((9841*19531*292561*(q4^2+q4+1))*m^2) := by ring
      _ ≤ D*((6561*15625*279841*q4^2)*sigma) := Nat.mul_le_mul_left D hlowercross
      _ = ((6561*15625*279841*q4^2)*p)*m^2 := by
        calc
          _ = (6561*15625*279841*q4^2)*(D*sigma) := by ring
          _ = (6561*15625*279841*q4^2)*(p*m^2) := by rw [hrel]
          _ = _ := by ring
  rcases hDcases with hDcase | hDcase | hDcase | hDcase
  all_goals rw [hDcase] at hp_eq huppercoef hlowercoef
  all_goals rw [hp_eq] at huppercoef hlowercoef
  all_goals rcases hqcases with hqcase | hqcase | hqcase
  all_goals rw [hqcase] at huppercoef hlowercoef
  all_goals norm_num at huppercoef
  all_goals norm_num at hlowercoef
