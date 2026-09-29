-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D75_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T21:25:01.087403+00:00
-- url     : https://prove2.me/submissions/70528961-749f-4daf-8bed-3615d5d6c13c

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 75)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hDq : D < q4) : False := by
  have hq4ge : 76 ≤ q4 := by omega
  let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 : Nat := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 : 2 * S3 < 3 * 3 ^ (2*a) := by
    simpa [S3] using OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
      (by norm_num) (by norm_num) (by norm_num)
  have h5 : 4 * S5 < 5 * 5 ^ (2*b) := by
    simpa [S5] using OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
      (by norm_num) (by norm_num) (by norm_num)
  have h23 : 22 * S23 < 23 * 23 ^ (2*c) := by
    simpa [S23] using OddPerfectNumber.geom_sum_cross_lt_of_le 23 23 (2*c)
      (by norm_num) (by norm_num) (by norm_num)
  have hq : 75 * Sq < 76 * q4 ^ (2*e) := by
    simpa [Sq] using OddPerfectNumber.geom_sum_cross_lt_of_le 76 q4 (2*e)
      (by norm_num) hq4ge hq4prime
  have hprod := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt h3 h5)
    (Nat.mul_lt_mul_of_lt_of_lt h23 hq)
  have hupper : 13200 * sigma < 26220 * m ^ 2 := by
    calc
      13200 * sigma = (2*S3) * (4*S5) * (22*S23) * (75*Sq) := by
        rw [hsigma]
        dsimp [S3, S5, S23, Sq]
        ring
      _ < (3 * 3^(2*a)) * (5 * 5^(2*b)) *
            (23 * 23^(2*c)) * (76 * q4^(2*e)) := by
        simpa only [mul_assoc] using hprod
      _ = 26220 * m ^ 2 := by
        rw [hfac]
        ring
  have hpval : p = 149 := by omega
  have hrel' : 75 * sigma = 149 * m ^ 2 := by
    calc
      75 * sigma = D * sigma := by rw [hD]
      _ = p * m ^ 2 := hrel
      _ = 149 * m ^ 2 := by rw [hpval]
  have hlow : 149 * m ^ 2 ≤ 75 * sigma := hrel'.symm.le
  have hscaled : 13200 * 149 * (m ^ 2) ≤ 13200 * (75 * sigma) := by
    calc
      13200 * 149 * (m ^ 2) = 13200 * (149 * (m ^ 2)) := by ring
      _ ≤ 13200 * (75 * sigma) := Nat.mul_le_mul_left 13200 hlow
  have hchain : 13200 * 149 * (m ^ 2) < 75 * 26220 * (m ^ 2) := by
    calc
      13200 * 149 * (m ^ 2) ≤ 13200 * (75 * sigma) := hscaled
      _ = 75 * (13200 * sigma) := by ring
      _ < 75 * (26220 * m ^ 2) := Nat.mul_lt_mul_of_pos_left hupper (by norm_num)
      _ = 75 * 26220 * (m ^ 2) := by ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hreverse : 75 * 26220 * (m ^ 2) < 13200 * 149 * (m ^ 2) := by
    have hc : 75 * 26220 < 13200 * 149 := by norm_num
    exact Nat.mul_lt_mul_of_pos_right hc hmpos
  exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt hreverse)) hchain)
