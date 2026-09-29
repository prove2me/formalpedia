-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_le_717
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T14:18:59.81399+00:00
-- url     : https://prove2.me/submissions/df112cc7-3b37-429a-94c0-40e91c8fc74b

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 27) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4) :
    q4 ≤ 717 := by
  by_contra hq4bad
  have hq4ge : 718 ≤ q4 := by omega
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
  have hq : 717 * Sq < 718 * q4 ^ (2*e) := by
    simpa [Sq] using OddPerfectNumber.geom_sum_cross_lt_of_le 718 q4 (2*e)
      (by norm_num) hq4ge hq4prime
  have h35 := Nat.mul_lt_mul_of_lt_of_lt h3 h5
  have h23q := Nat.mul_lt_mul_of_lt_of_lt h23 hq
  have hprod := Nat.mul_lt_mul_of_lt_of_lt h35 h23q
  have hupper : 126192 * sigma < 247710 * m ^ 2 := by
    calc
      126192 * sigma = (2*S3) * (4*S5) * (22*S23) * (717*Sq) := by
        rw [hsigma]
        dsimp [S3, S5, S23, Sq]
        ring
      _ < (3 * 3^(2*a)) * (5 * 5^(2*b)) *
            (23 * 23^(2*c)) * (718 * q4^(2*e)) := by
        simpa only [mul_assoc] using hprod
      _ = 247710 * m ^ 2 := by
        rw [hfac]
        ring
  have hpval : p = 53 := by omega
  have hrel' : 27 * sigma = 53 * m ^ 2 := by
    calc
      27 * sigma = D * sigma := by rw [hD]
      _ = p * m ^ 2 := hrel
      _ = 53 * m ^ 2 := by rw [hpval]
  have hlow : 53 * m ^ 2 ≤ 27 * sigma := hrel'.symm.le
  have hscaled : 126192 * 53 * (m ^ 2) ≤ 126192 * (27 * sigma) := by
    calc
      126192 * 53 * (m ^ 2) = 126192 * (53 * (m ^ 2)) := by ring
      _ ≤ 126192 * (27 * sigma) := Nat.mul_le_mul_left 126192 hlow
  have hchain : 126192 * 53 * (m ^ 2) < 27 * 247710 * (m ^ 2) := by
    calc
      126192 * 53 * (m ^ 2) ≤ 126192 * (27 * sigma) := hscaled
      _ = 27 * (126192 * sigma) := by ring
      _ < 27 * (247710 * m ^ 2) := Nat.mul_lt_mul_of_pos_left hupper (by norm_num)
      _ = 27 * 247710 * (m ^ 2) := by ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hreverse : 27 * 247710 * (m ^ 2) < 126192 * 53 * (m ^ 2) := by
    have hc : 27 * 247710 < 126192 * 53 := by norm_num
    exact Nat.mul_lt_mul_of_pos_right hc hmpos
  exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt hreverse)) hchain)
