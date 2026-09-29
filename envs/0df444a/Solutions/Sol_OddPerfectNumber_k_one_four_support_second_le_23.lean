-- Prove2me | solution 1 for OddPerfectNumber.k_one_four_support_second_le_23
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T18:20:40.865133+00:00
-- url     : https://prove2.me/submissions/0bd97ec7-405a-41c5-b7f8-6d3df9e9275e

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_four_support_local_product_upper
import Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion

theorem solution (p m d q1 q2 q3 q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : m.primeFactors = {q1, q2, q3, q4})
    (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime) (hq4 : q4.Prime)
    (horder : q1 < q2 ∧ q2 < q3 ∧ q3 < q4)
    (hq1eq : q1 = 3) :
    q2 ≤ 23 := by
  rcases horder with ⟨h12, h23, h34⟩
  by_contra hq2bad
  have hq2ge : 29 ≤ q2 := by
    have hq2lo : 24 ≤ q2 := by omega
    by_contra h
    have hq2hi : q2 ≤ 28 := by omega
    interval_cases q2 <;> norm_num at hq2
  have hne12 : q1 ≠ q2 := by omega
  have hne13 : q1 ≠ q3 := by omega
  have hne14 : q1 ≠ q4 := by omega
  have hne23 : q2 ≠ q3 := by omega
  have hne24 : q2 ≠ q4 := by omega
  have hne34 : q3 ≠ q4 := by omega
  have hq3ge : 31 ≤ q3 := by
    have hq3lo : 30 ≤ q3 := by omega
    by_contra h
    have hq3le : q3 ≤ 30 := by omega
    have hq3eq : q3 = 30 := by omega
    subst q3
    norm_num at hq3
  have hq4ge : 37 ≤ q4 := by
    have hq4lo : 32 ≤ q4 := by omega
    by_contra h
    have hq4le : q4 ≤ 36 := by omega
    interval_cases q4 <;> norm_num at hq4
  have hm0 : m ≠ 0 := by
    obtain ⟨u, hu⟩ := hm
    omega
  have hm2ne : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hm2support : (m ^ 2).primeFactors = m.primeFactors := by
    rw [Nat.primeFactors_pow m (by norm_num)]
  have hsupport2 : (m ^ 2).primeFactors = {q1, q2, q3, q4} :=
    hm2support.trans hsupport
  have hm2odd : Odd (m ^ 2) := hm.pow
  let S : Nat → Nat := fun q =>
    ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i
  have hsumprod :
      (∑ x ∈ (m ^ 2).divisors, x) =
        ∏ q ∈ (m ^ 2).primeFactors, S q := by
    have hsum : (∑ x ∈ (m ^ 2).divisors, x) =
        ArithmeticFunction.sigma 1 (m ^ 2) :=
      (ArithmeticFunction.sigma_one_apply (m ^ 2)).symm
    have hprod' : ArithmeticFunction.sigma 1 (m ^ 2) =
        ∏ q ∈ (m ^ 2).primeFactors,
          ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
      simpa only [mul_one] using
        ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) (n := m ^ 2) hm2ne
    rw [hsum, hprod']
  have hsumprod4 :
      (∑ x ∈ (m ^ 2).divisors, x) = S q1 * S q2 * S q3 * S q4 := by
    rw [hsumprod, hsupport2]
    simp [S, hne12, hne13, hne14, hne23, hne24, hne34, mul_assoc]
  have hfac : m ^ 2 =
      q1 ^ ((m ^ 2).factorization q1) *
        q2 ^ ((m ^ 2).factorization q2) *
        q3 ^ ((m ^ 2).factorization q3) *
        q4 ^ ((m ^ 2).factorization q4) := by
    exact OddPerfectNumber.four_support_factorization_expansion
      (m ^ 2) q1 q2 q3 q4 hm2ne hsupport2
      hne12 hne13 hne14 hne23 hne24 hne34
  have hi1 : 2 * S q1 < 3 * q1 ^ ((m ^ 2).factorization q1) := by
    dsimp [S]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 3 q1
      ((m ^ 2).factorization q1) (by norm_num) (by omega) hq1
  have hi2 : 28 * S q2 < 29 * q2 ^ ((m ^ 2).factorization q2) := by
    dsimp [S]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 29 q2
      ((m ^ 2).factorization q2) (by norm_num) hq2ge hq2
  have hi3 : 30 * S q3 < 31 * q3 ^ ((m ^ 2).factorization q3) := by
    dsimp [S]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 31 q3
      ((m ^ 2).factorization q3) (by norm_num) hq3ge hq3
  have hi4 : 36 * S q4 < 37 * q4 ^ ((m ^ 2).factorization q4) := by
    dsimp [S]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 37 q4
      ((m ^ 2).factorization q4) (by norm_num) hq4ge hq4
  have hmul12 := Nat.mul_lt_mul_of_lt_of_lt hi1 hi2
  have hmul123 := Nat.mul_lt_mul_of_lt_of_lt hmul12 hi3
  have hmul1234 := Nat.mul_lt_mul_of_lt_of_lt hmul123 hi4
  have hupper : 60480 * (∑ x ∈ (m ^ 2).divisors, x) < 99789 * m ^ 2 := by
    calc
      60480 * (∑ x ∈ (m ^ 2).divisors, x) =
          60480 * (S q1 * S q2 * S q3 * S q4) := by rw [hsumprod4]
      _ = (2 * S q1) * (28 * S q2) *
          (30 * S q3) * (36 * S q4) := by ring
      _ < (3 * q1 ^ ((m ^ 2).factorization q1)) *
          (29 * q2 ^ ((m ^ 2).factorization q2)) *
          (31 * q3 ^ ((m ^ 2).factorization q3)) *
          (37 * q4 ^ ((m ^ 2).factorization q4)) := hmul1234
      _ = 99789 *
          (q1 ^ ((m ^ 2).factorization q1) *
            q2 ^ ((m ^ 2).factorization q2) *
            q3 ^ ((m ^ 2).factorization q3) *
            q4 ^ ((m ^ 2).factorization q4)) := by ring
      _ = 99789 * m ^ 2 := by
        exact congrArg (fun z : Nat => 99789 * z) hfac.symm
  let D := (p + 1) / 2
  have hDprod : m ^ 2 = D * d := by simpa [D] using hprod
  have hcoef : 5 * D ≤ 3 * p := by
    dsimp [D]
    have hpge : 5 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      by_contra h
      have hple : p ≤ 4 := by omega
      interval_cases p <;> norm_num at hp4
    omega
  have hscaled : 5 * m ^ 2 ≤ 3 * (∑ x ∈ (m ^ 2).divisors, x) := by
    calc
      5 * m ^ 2 = (5 * D) * d := by rw [hDprod]; ring
      _ ≤ (3 * p) * d := Nat.mul_le_mul_right d hcoef
      _ = 3 * (p * d) := by ring
      _ = 3 * (∑ x ∈ (m ^ 2).divisors, x) := by rw [hsig]
  have hlower : 100800 * m ^ 2 ≤ 60480 * (∑ x ∈ (m ^ 2).divisors, x) := by
    calc
      100800 * m ^ 2 = 20160 * (5 * m ^ 2) := by ring
      _ ≤ 20160 * (3 * (∑ x ∈ (m ^ 2).divisors, x)) :=
        Nat.mul_le_mul_left 20160 hscaled
      _ = 60480 * (∑ x ∈ (m ^ 2).divisors, x) := by ring
  have hm2pos : 0 < m ^ 2 := by
    obtain ⟨u, hu⟩ := hm
    omega
  have hcoef2 : 99789 * m ^ 2 ≤ 100800 * m ^ 2 := by
    exact Nat.mul_le_mul_right (m ^ 2) (by norm_num)
  have hupper' : 60480 * (∑ x ∈ (m ^ 2).divisors, x) <
      100800 * m ^ 2 := lt_of_lt_of_le hupper hcoef2
  exact (Nat.not_lt_of_ge hlower) hupper'
