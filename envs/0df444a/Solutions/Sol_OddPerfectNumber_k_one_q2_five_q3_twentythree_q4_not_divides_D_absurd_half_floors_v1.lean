-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_half_floors_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T14:19:20.471406+00:00
-- url     : https://prove2.me/submissions/6bff0d21-907e-4ae0-b2c6-73408c77eb7e

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_not_divides_D_cases_v1
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full floors 8,6,4,2.
-- This is the small-D nondivisor arm, not a complete canonical branch.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hq4notdiv : ¬ q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (hq4le : q4 ≤ D) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c)
    (he : 1 ≤ e) : False := by
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_not_divides_D_cases_v1
    D p q4 hDlt hDodd hp hp_eq hq4prime hq4gt hq4notdiv hDsupport
  have hDhi : D ≤ 75 := by omega
  have hq73 : q4 ≤ 73 := by
    by_contra hbad
    have hlo : 74 ≤ q4 := by omega
    have hhi : q4 ≤ 75 := by omega
    interval_cases q4 <;> norm_num at hq4prime
  let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 : Nat := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow23 : 23 ^ 4 ≤ 23 ^ (2*c) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
  have h23 : 292561 * 23 ^ (2*c) ≤ 279841 * S23 := by
    dsimp [S23]
    omega
  have hlast := OddPerfectNumber.geom_sum_last_two_terms_le q4 (2*e) (by omega)
  have hpowq : q4 ^ (2*e) ≤ 73 * q4 ^ (2*e - 1) := by
    rw [show 2*e = (2*e - 1) + 1 by omega, pow_succ]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (q4 ^ (2*e - 1)) hq73
  have hq : 74 * q4 ^ (2*e) ≤ 73 * Sq := by
    have ht := Nat.mul_le_mul_left 73 hlast
    dsimp [Sq]
    omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) (Nat.mul_le_mul h23 hq)
  have hcross : 4161135550728494 * m ^ 2 ≤ 2094229476140625 * sigma := by
    calc
      4161135550728494 * m ^ 2 =
          (9841*3^(2*a)) * (19531*5^(2*b)) *
            ((292561*23^(2*c)) * (74*q4^(2*e))) := by rw [hfac]; ring
      _ ≤ (6561*S3) * (15625*S5) * ((279841*S23) * (73*Sq)) := by
        simpa only [S3, S5, S23, Sq] using hmul
      _ = 2094229476140625 * sigma := by rw [hsigma]; ring
  have hmpos : 0 < m ^ 2 := by rw [hfac]; positivity
  have hineq : (4161135550728494 * D) * m ^ 2 ≤
      (2094229476140625 * p) * m ^ 2 := by
    calc
      (4161135550728494 * D) * m ^ 2 = D * (4161135550728494 * m ^ 2) := by ring
      _ ≤ D * (2094229476140625 * sigma) := Nat.mul_le_mul_left D hcross
      _ = 2094229476140625 * (D * sigma) := by ring
      _ = 2094229476140625 * (p * m ^ 2) := by rw [hrel]
      _ = (2094229476140625 * p) * m ^ 2 := by ring
  have hcancel := Nat.le_of_mul_le_mul_right hineq hmpos
  omega
