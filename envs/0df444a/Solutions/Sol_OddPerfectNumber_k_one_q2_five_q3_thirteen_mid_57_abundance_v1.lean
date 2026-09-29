-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_57_abundance_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:39:24.968984+00:00
-- url     : https://prove2.me/submissions/7cea88d8-454e-45ed-b090-6aeb8f2c9c28

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_two_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 57) (hp_eq : p = 113) (hq4eq : q4 = 19)
    (ha : 1 ≤ a) (hb : 4 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    False := by
  subst hD; subst hp_eq; subst hq4eq
  -- Accepted sharp lower bounds for the 3- and 13-components (full exponents 2a, 2c).
  have l3 : 13 * 3 ^ (2*a) ≤ 9 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) :=
    OddPerfectNumber.geom_ratio_lower_three_ge_two_sharp (2*a) (by omega)
  have l13 : 183 * 13 ^ (2*c) ≤ 169 * (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) :=
    OddPerfectNumber.geom_ratio_lower_thirteen_ge_two (2*c) (by omega)
  -- 5-component: lift the exact value at full exponent 8 by range-splitting.
  have hS9 : (∑ i ∈ Finset.range 9, 5 ^ i) = 488281 := by
    norm_num [Finset.sum_range_succ]
  have h59 : (5:ℕ) ^ 9 = 1953125 := by norm_num
  have hsplit5 : (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)
      = 488281 + 1953125 * (∑ j ∈ Finset.range (2*b - 8), 5 ^ j) := by
    have h9 : 2*b + 1 = 9 + (2*b - 8) := by omega
    have hstep : (∑ i ∈ Finset.range (9 + (2*b - 8)), 5 ^ i)
        = (∑ i ∈ Finset.range 9, 5 ^ i)
          + 5 ^ 9 * (∑ j ∈ Finset.range (2*b - 8), 5 ^ j) := by
      rw [Finset.sum_range_add, Finset.mul_sum, add_left_cancel_iff]
      exact Finset.sum_congr rfl (fun j _ => by rw [pow_add])
    rw [h9, hstep, hS9, h59]
  have key5 : ∀ k : Nat, 4 * (∑ i ∈ Finset.range k, 5 ^ i) + 1 = 5 ^ k := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega
  have hR5 := key5 (2*b - 8)
  have hA5 : 5 ^ (2*b) = 390625 * 5 ^ (2*b - 8) := by
    have h2b : 2*b = 8 + (2*b - 8) := by omega
    conv_lhs => rw [h2b, pow_add]
    rw [show (5:ℕ) ^ 8 = 390625 by norm_num]
  have l5 : 488281 * 5 ^ (2*b)
      ≤ 390625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) := by
    omega
  -- 19-component: lift the exact value at full exponent 2 by range-splitting.
  have hS3 : (∑ i ∈ Finset.range 3, 19 ^ i) = 381 := by
    norm_num [Finset.sum_range_succ]
  have h173 : (19:ℕ) ^ 3 = 6859 := by norm_num
  have hsplit17 : (∑ i ∈ Finset.range (2*e + 1), 19 ^ i)
      = 381 + 6859 * (∑ j ∈ Finset.range (2*e - 2), 19 ^ j) := by
    have h3 : 2*e + 1 = 3 + (2*e - 2) := by omega
    have hstep : (∑ i ∈ Finset.range (3 + (2*e - 2)), 19 ^ i)
        = (∑ i ∈ Finset.range 3, 19 ^ i)
          + 19 ^ 3 * (∑ j ∈ Finset.range (2*e - 2), 19 ^ j) := by
      rw [Finset.sum_range_add, Finset.mul_sum, add_left_cancel_iff]
      exact Finset.sum_congr rfl (fun j _ => by rw [pow_add])
    rw [h3, hstep, hS3, h173]
  have key17 : ∀ k : Nat, 18 * (∑ i ∈ Finset.range k, 19 ^ i) + 1 = 19 ^ k := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega
  have hR17 := key17 (2*e - 2)
  have hA17 : 19 ^ (2*e) = 361 * 19 ^ (2*e - 2) := by
    have h2e : 2*e = 2 + (2*e - 2) := by omega
    conv_lhs => rw [h2e, pow_add]
    rw [show (19:ℕ) ^ 2 = 361 by norm_num]
  have l17 : 381 * 19 ^ (2*e)
      ≤ 361 * (∑ i ∈ Finset.range (2*e + 1), 19 ^ i) := by
    omega
  -- Multiply the four cross-multiplied bounds and rearrange to C * sigma >= K * m^2.
  have h34 := Nat.mul_le_mul l3 l5
  have h56 := Nat.mul_le_mul l13 l17
  have hmul := Nat.mul_le_mul h34 h56
  have e1 : (13 * 3 ^ (2*a)) * (488281 * 5 ^ (2*b)) * ((183 * 13 ^ (2*c)) * (381 * 19 ^ (2*e)))
      = 442577410119 * m ^ 2 := by
    rw [hfac]; ring
  have e2 : (9 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (390625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)) *
      ((169 * (∑ i ∈ Finset.range (2*c + 1), 13 ^ i)) * (361 * (∑ i ∈ Finset.range (2*e + 1), 19 ^ i)))
      = 214484765625 * sigma := by
    rw [hsigma]; ring
  rw [e1, e2] at hmul
  have hm2 : 0 < m ^ 2 := by
    rw [hfac]; positivity
  omega
