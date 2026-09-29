-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_q4_lt_500_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T14:27:24.393987+00:00
-- url     : https://prove2.me/submissions/e04271f0-ca7e-47cf-bc6a-ac83926ebc4b

import Mathlib

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hq4 : q4.Prime) (hq4gt : 17 < q4)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hD : D = 289) :
    q4 < 500 := by
  subst hD
  have hp577 : p = 577 := by omega
  subst hp577
  have hq4pos : 1 ≤ q4 := by omega
  -- geometric-sum identities: (base-1) * S + 1 = base^(len)
  have g3 : 2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) + 1 = 3 ^ (2*a + 1) := by
    rw [mul_comm 2 _]
    exact geom_sum_mul_add 2 (2*a + 1)
  have g5 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) + 1 = 5 ^ (2*b + 1) := by
    rw [mul_comm 4 _]
    exact geom_sum_mul_add 4 (2*b + 1)
  have g17 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) + 1 = 17 ^ (2*c + 1) := by
    rw [mul_comm 16 _]
    exact geom_sum_mul_add 16 (2*c + 1)
  have gq : (q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) + 1 = q4 ^ (2*e + 1) := by
    have h := geom_sum_mul_add (q4 - 1) (2*e + 1)
    rw [Nat.sub_add_cancel hq4pos] at h
    rw [mul_comm (q4 - 1) _]
    exact h
  -- strict upper bounds on each factor
  have e1 : 2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) < 3 ^ (2*a + 1) := by omega
  have e2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) < 5 ^ (2*b + 1) := by omega
  have e3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) < 17 ^ (2*c + 1) := by omega
  have e4 : (q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) < q4 ^ (2*e + 1) := by omega
  have l2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) ≤ 5 ^ (2*b + 1) := by omega
  have l3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) ≤ 17 ^ (2*c + 1) := by omega
  have l4 : (q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) ≤ q4 ^ (2*e + 1) := by omega
  have hBpos : 0 < 5 ^ (2*b + 1) := by positivity
  have hCpos : 0 < 17 ^ (2*c + 1) := by positivity
  have hEpos : 0 < q4 ^ (2*e + 1) := by positivity
  -- four-factor strict product bound
  have p1 : (2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))
      < 3 ^ (2*a + 1) * 5 ^ (2*b + 1) :=
    Nat.mul_lt_mul_of_lt_of_le e1 l2 hBpos
  have p2 : ((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)))
        * (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))
      < (3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1) :=
    Nat.mul_lt_mul_of_lt_of_le p1 l3 hCpos
  have p3 : (((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)))
        * (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))) * ((q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
      < ((3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1)) * q4 ^ (2*e + 1) :=
    Nat.mul_lt_mul_of_lt_of_le p2 l4 hEpos
  -- bridge variable exponents to factored form
  have r3 : (3 : ℕ) ^ (2*a + 1) = 3 ^ (2*a) * 3 := pow_succ 3 (2*a)
  have r5 : (5 : ℕ) ^ (2*b + 1) = 5 ^ (2*b) * 5 := pow_succ 5 (2*b)
  have r17 : (17 : ℕ) ^ (2*c + 1) = 17 ^ (2*c) * 17 := pow_succ 17 (2*c)
  have rq : q4 ^ (2*e + 1) = q4 ^ (2*e) * q4 := pow_succ q4 (2*e)
  have p3b := p3
  rw [r3, r5, r17, rq] at p3b
  -- transport to the sigma relation
  have fin : 128 * (q4 - 1) * 289 * sigma < 289 * 255 * q4 * m ^ 2 := by
    rw [hsigma, hfac]
    linear_combination 289 * p3b
  have hm2 : 0 < m ^ 2 := by rw [hfac]; positivity
  have fin2 : (128 * (q4 - 1) * 577) * m ^ 2 < (289 * 255 * q4) * m ^ 2 := by
    have hrw : 128 * (q4 - 1) * 289 * sigma = (128 * (q4 - 1) * 577) * m ^ 2 := by
      linear_combination 128 * (q4 - 1) * hrel
    rw [← hrw]
    exact fin
  have fin3 : 128 * (q4 - 1) * 577 < 289 * 255 * q4 :=
    lt_of_mul_lt_mul_right fin2 (le_of_lt hm2)
  omega
