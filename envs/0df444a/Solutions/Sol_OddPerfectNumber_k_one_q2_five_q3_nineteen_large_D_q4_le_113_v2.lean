-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_le_113_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T14:03:12.207522+00:00
-- url     : https://prove2.me/submissions/420f05fe-401e-418c-ba8f-20ce8f3cceb1

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 225 ≤ D) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4) :
    q4 ≤ 113 := by
  by_contra hq4bad
  have hq4gt113 : 113 < q4 := by omega
  have hq4ge : 127 ≤ q4 := by
    by_contra h
    have hle : q4 ≤ 126 := by omega
    interval_cases q4 <;> norm_num at hq4prime
  let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S19 : Nat := ∑ i ∈ Finset.range (2*c + 1), 19 ^ i
  let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 : 2 * S3 < 3 * 3 ^ (2*a) := by
    simpa [S3] using
      OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
        (by norm_num) (by norm_num) (by norm_num)
  have h5 : 4 * S5 < 5 * 5 ^ (2*b) := by
    simpa [S5] using
      OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
        (by norm_num) (by norm_num) (by norm_num)
  have h19 : 18 * S19 < 19 * 19 ^ (2*c) := by
    simpa [S19] using
      OddPerfectNumber.geom_sum_cross_lt_of_le 19 19 (2*c)
        (by norm_num) (by norm_num) (by norm_num)
  have hq : 126 * Sq < 127 * q4 ^ (2*e) := by
    simpa [Sq] using
      OddPerfectNumber.geom_sum_cross_lt_of_le 127 q4 (2*e)
        (by norm_num) hq4ge hq4prime
  have h35 := Nat.mul_lt_mul_of_lt_of_lt h3 h5
  have h19q := Nat.mul_lt_mul_of_lt_of_lt h19 hq
  have hprod := Nat.mul_lt_mul_of_lt_of_lt h35 h19q
  have hupper : 18144 * sigma < 36195 * m ^ 2 := by
    calc
      18144 * sigma = (2*S3) * (4*S5) * (18*S19) * (126*Sq) := by
        rw [hsigma]
        dsimp [S3, S5, S19, Sq]
        ring
      _ < (3 * 3^(2*a)) * (5 * 5^(2*b)) *
            (19 * 19^(2*c)) * (127 * q4^(2*e)) := by
        simpa only [mul_assoc] using hprod
      _ = 36195 * m ^ 2 := by
        rw [hfac]
        ring
  have hcoef : 449 * D ≤ 225 * p := by
    omega
  have hcross := Nat.mul_le_mul_right sigma hcoef
  have hp_pos : 0 < p := by
    rw [hp_eq]
    omega
  have hlow : 449 * m ^ 2 ≤ 225 * sigma := by
    apply le_of_mul_le_mul_left ?_ hp_pos
    calc
      p * (449 * m ^ 2) = 449 * (p * m ^ 2) := by ring
      _ = 449 * (D * sigma) := by rw [hrel]
      _ = 449 * D * sigma := by ring
      _ ≤ 225 * p * sigma := hcross
      _ = p * (225 * sigma) := by ring
  have hscaled : 18144 * 449 * (m ^ 2) ≤ 18144 * (225 * sigma) := by
    calc
      18144 * 449 * (m ^ 2) = 18144 * (449 * (m ^ 2)) := by ring
      _ ≤ 18144 * (225 * sigma) := Nat.mul_le_mul_left 18144 hlow
  have hupper_scaled := Nat.mul_lt_mul_of_pos_left hupper (by norm_num : 0 < 225)
  have hchain : 18144 * 449 * (m ^ 2) < 225 * 36195 * (m ^ 2) := by
    calc
      18144 * 449 * (m ^ 2) ≤ 18144 * (225 * sigma) := hscaled
      _ = 225 * (18144 * sigma) := by ring
      _ < 225 * (36195 * m ^ 2) := hupper_scaled
      _ = 225 * 36195 * (m ^ 2) := by ring
  have hconst : 18144 * 449 > 225 * 36195 := by norm_num
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hreverse : 225 * 36195 * (m ^ 2) < 18144 * 449 * (m ^ 2) := by
    exact Nat.mul_lt_mul_of_pos_right hconst hmpos
  exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt hreverse)) hchain)
