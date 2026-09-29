-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_gt_141_self_cases_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T21:05:32.490667+00:00
-- url     : https://prove2.me/submissions/f09325e4-298d-46f8-bf18-3290e6b48128

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_factor_support_form_v4
import Theorems.Thm_OddPerfectNumber_q3_nineteen_prime_pair_142_224_cases_v1

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 147 ≤ D) (hDlt : D < 225)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4ge : 142 ≤ q4)
    (hq4leD : q4 ≤ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) :
    (D = 157 ∧ q4 = 157 ∧ p = 313) ∨
      (D = 199 ∧ q4 = 199 ∧ p = 397) ∨
      (D = 211 ∧ q4 = 211 ∧ p = 421) := by
  have hDdvd : D ∣ m ^ 2 :=
    OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
      m D p sigma hrel hp hp_eq
  have hDpos : 0 < D := by omega
  obtain ⟨i, j, k, l, hform, hi0, hj0, hk0, hl0⟩ :=
    OddPerfectNumber.k_one_q2_five_q3_nineteen_D_factor_support_form_v4
      m a b c e D q4 hfac hDdvd hDpos hq4prime hq4gt hDsupport
  have hi : i ≤ 4 := by
    by_contra hn
    have hge : 5 ≤ i := by omega
    have hpow : 243 ≤ 3^i := by
      calc
        243 = 3^5 := by norm_num
        _ ≤ 3^i := Nat.pow_le_pow_right (by norm_num) hge
    have hle : 3^i ≤ D := by
      rw [hform]
      have hpos : 0 < 5^j * 19^k * q4^l := by positivity
      simpa [Nat.mul_assoc] using Nat.le_mul_of_pos_right (3^i) hpos
    omega
  have hj : j ≤ 3 := by
    by_contra hn
    have hge : 4 ≤ j := by omega
    have hpow : 625 ≤ 5^j := by
      calc
        625 = 5^4 := by norm_num
        _ ≤ 5^j := Nat.pow_le_pow_right (by norm_num) hge
    have hle : 5^j ≤ D := by
      rw [hform]
      have hpos : 0 < 3^i * 19^k * q4^l := by positivity
      have hbase : 5^j ≤ 5^j * (3^i * 19^k * q4^l) :=
        Nat.le_mul_of_pos_right (5^j) hpos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbase
    omega
  have hk : k ≤ 1 := by
    by_contra hn
    have hge : 2 ≤ k := by omega
    have hpow : 361 ≤ 19^k := by
      calc
        361 = 19^2 := by norm_num
        _ ≤ 19^k := Nat.pow_le_pow_right (by norm_num) hge
    have hle : 19^k ≤ D := by
      rw [hform]
      have hpos : 0 < 3^i * 5^j * q4^l := by positivity
      have hbase : 19^k ≤ 19^k * (3^i * 5^j * q4^l) :=
        Nat.le_mul_of_pos_right (19^k) hpos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbase
    omega
  have hl : l ≤ 1 := by
    by_contra hn
    have hge : 2 ≤ l := by omega
    have hqpos : 0 < q4 := by omega
    have hpow : 20164 ≤ q4^l := by
      calc
        20164 = 142^2 := by norm_num
        _ ≤ q4^2 := Nat.pow_le_pow_left hq4ge 2
        _ ≤ q4^l := Nat.pow_le_pow_right hqpos hge
    have hle : q4^l ≤ D := by
      rw [hform]
      have hpos : 0 < 3^i * 5^j * 19^k := by positivity
      have hbase : q4^l ≤ q4^l * (3^i * 5^j * 19^k) :=
        Nat.le_mul_of_pos_right (q4^l) hpos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbase
    omega
  interval_cases l
  · clear hi0 hj0 hk0
    interval_cases i <;> interval_cases j <;> interval_cases k
    all_goals norm_num [pow_succ] at hform
    all_goals have hD171 : D = 171 := by omega
    all_goals subst D
    all_goals norm_num at hp_eq
    all_goals rw [hp_eq] at hp
    all_goals norm_num at hp
    all_goals omega
  · have hprod : D = q4 * (3^i * 5^j * 19^k) := by
      simpa [pow_one, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hform
    let H := 3^i * 5^j * 19^k
    have hHpos : 1 ≤ H := by
      dsimp [H]
      have hpos : 0 < 3^i * 5^j * 19^k := by positivity
      omega
    have hHle : H ≤ 1 := by
      by_contra hn
      have hH2 : 2 ≤ H := by omega
      have hmul : q4 * 2 ≤ q4 * H := Nat.mul_le_mul_left q4 hH2
      have hDge : 2 * q4 ≤ D := by
        calc
          2 * q4 = q4 * 2 := by ring
          _ ≤ q4 * H := hmul
          _ = D := by simpa [H] using hprod.symm
      omega
    have hHeq : H = 1 := by omega
    have hDq : D = q4 := by
      calc
        D = q4 * H := by simpa [H] using hprod
        _ = q4 := by simp [hHeq]
    have hpq : p = 2 * q4 - 1 := by omega
    have hq4upper : q4 ≤ 224 := by omega
    have hqcases := OddPerfectNumber.q3_nineteen_prime_pair_142_224_cases_v1
      q4 p hq4prime hp hpq hq4ge hq4upper
    rcases hqcases with h157 | h199 | h211
    · exact Or.inl ⟨by omega, h157, by omega⟩
    · exact Or.inr (Or.inl ⟨by omega, h199, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h211, by omega⟩)
