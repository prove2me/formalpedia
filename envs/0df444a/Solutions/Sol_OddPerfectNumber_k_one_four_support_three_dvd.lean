-- Prove2me | solution 1 for OddPerfectNumber.k_one_four_support_three_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T18:19:16.39968+00:00
-- url     : https://prove2.me/submissions/4dc50758-3503-4152-8c58-997fd28d3f9a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_four_support_local_product_upper
import Theorems.Thm_OddPerfectNumber_four_support_scaled_abundance_contradiction
import Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion

theorem solution (p m d : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hcard : m.primeFactors.card = 4) :
    3 ∣ m := by
  by_contra h3
  have hm0 : m ≠ 0 := by
    obtain ⟨u, hu⟩ := hm
    omega
  have hm2ne : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hm2pos : 0 < m ^ 2 := pow_pos (by omega) _
  have hm2support : (m ^ 2).primeFactors = m.primeFactors := by
    rw [Nat.primeFactors_pow m (by norm_num)]
  have hlen : (m.primeFactors.sort (· ≤ ·)).length = 4 := by
    rw [Finset.length_sort, hcard]
  obtain ⟨q1, q2, q3, q4, hlist⟩ := List.length_eq_four.mp hlen
  have hsorted : (m.primeFactors.sort (· ≤ ·)).SortedLT :=
    Finset.sortedLT_sort m.primeFactors
  have hpair : (m.primeFactors.sort (· ≤ ·)).Pairwise (· < ·) :=
    hsorted.pairwise
  rw [hlist] at hpair
  have h12 : q1 < q2 := by
    exact (List.pairwise_cons.mp hpair).1 q2 (by simp)
  have htail : (q2 :: q3 :: q4 :: []).Pairwise (· < ·) :=
    (List.pairwise_cons.mp hpair).2
  have h23 : q2 < q3 := by
    exact (List.pairwise_cons.mp htail).1 q3 (by simp)
  have htail' : (q3 :: q4 :: []).Pairwise (· < ·) :=
    (List.pairwise_cons.mp htail).2
  have h34 : q3 < q4 := by
    exact (List.pairwise_cons.mp htail').1 q4 (by simp)
  have hset : (m.primeFactors.sort (· ≤ ·)).toFinset = m.primeFactors :=
    Finset.sort_toFinset _ _
  rw [hlist] at hset
  have hq1mem : q1 ∈ m.primeFactors := by rw [← hset]; simp
  have hq2mem : q2 ∈ m.primeFactors := by rw [← hset]; simp
  have hq3mem : q3 ∈ m.primeFactors := by rw [← hset]; simp
  have hq4mem : q4 ∈ m.primeFactors := by rw [← hset]; simp
  have hq1 : q1.Prime := Nat.prime_of_mem_primeFactors hq1mem
  have hq2 : q2.Prime := Nat.prime_of_mem_primeFactors hq2mem
  have hq3 : q3.Prime := Nat.prime_of_mem_primeFactors hq3mem
  have hq4 : q4.Prime := Nat.prime_of_mem_primeFactors hq4mem
  have hne12 : q1 ≠ q2 := Nat.ne_of_lt h12
  have hne13 : q1 ≠ q3 := by omega
  have hne14 : q1 ≠ q4 := by omega
  have hne23 : q2 ≠ q3 := Nat.ne_of_lt h23
  have hne24 : q2 ≠ q4 := by omega
  have hne34 : q3 ≠ q4 := Nat.ne_of_lt h34
  have hsupport : m.primeFactors = {q1, q2, q3, q4} := by
    simpa [Finset.mem_insert, hne12, hne13, hne14, hne23, hne24, hne34] using hset.symm
  have hsupport2 : (m ^ 2).primeFactors = {q1, q2, q3, q4} :=
    hm2support.trans hsupport
  have hm2odd : Odd (m ^ 2) := hm.pow
  have hq1ne2 : q1 ≠ 2 := by
    intro hq
    subst q1
    obtain ⟨u, hu⟩ := hm
    have h2m : 2 ∣ m := by
      exact Nat.dvd_of_mem_primeFactors hq1mem
    omega
  have hq1ne3 : q1 ≠ 3 := by
    intro hq
    subst q1
    exact h3 (Nat.dvd_of_mem_primeFactors hq1mem)
  have hq1ge : 5 ≤ q1 := by
    have hq1two : 2 ≤ q1 := hq1.two_le
    by_contra h
    have hq1le : q1 ≤ 4 := by omega
    have hq1ne4 : q1 ≠ 4 := by
      intro hq
      subst q1
      norm_num at hq1
    omega
  have hq2ge : 7 ≤ q2 := by
    have hq2two : 2 ≤ q2 := hq2.two_le
    have hq2lo : 6 ≤ q2 := by omega
    by_contra h
    have hq2le : q2 ≤ 6 := by omega
    interval_cases q2 <;> norm_num at hq2
  have hq3ge : 11 ≤ q3 := by
    have hq3two : 2 ≤ q3 := hq3.two_le
    have hq3lo : 8 ≤ q3 := by omega
    by_contra h
    have hq3le : q3 ≤ 10 := by omega
    interval_cases q3 <;> norm_num at hq3
  have hq4ge : 13 ≤ q4 := by
    have hq4two : 2 ≤ q4 := hq4.two_le
    have hq4lo : 12 ≤ q4 := by omega
    by_contra h
    have hq4le : q4 ≤ 12 := by omega
    interval_cases q4 <;> norm_num at hq4
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
  have hi1 : 4 * S q1 < 5 * q1 ^ ((m ^ 2).factorization q1) := by
    dsimp [S]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 5 q1
      ((m ^ 2).factorization q1) (by norm_num) hq1ge hq1
  have hi2 : 6 * S q2 < 7 * q2 ^ ((m ^ 2).factorization q2) := by
    dsimp [S]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 7 q2
      ((m ^ 2).factorization q2) (by norm_num) hq2ge hq2
  have hi3 : 10 * S q3 < 11 * q3 ^ ((m ^ 2).factorization q3) := by
    dsimp [S]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 11 q3
      ((m ^ 2).factorization q3) (by norm_num) hq3ge hq3
  have hi4 : 12 * S q4 < 13 * q4 ^ ((m ^ 2).factorization q4) := by
    dsimp [S]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 13 q4
      ((m ^ 2).factorization q4) (by norm_num) hq4ge hq4
  have hmul12 := Nat.mul_lt_mul_of_lt_of_lt hi1 hi2
  have hmul123 := Nat.mul_lt_mul_of_lt_of_lt hmul12 hi3
  have hmul1234 := Nat.mul_lt_mul_of_lt_of_lt hmul123 hi4
  have hupper : 2880 * (∑ x ∈ (m ^ 2).divisors, x) < 5005 * m ^ 2 := by
    calc
      2880 * (∑ x ∈ (m ^ 2).divisors, x) =
          2880 * (S q1 * S q2 * S q3 * S q4) := by rw [hsumprod4]
      _ < 5005 * (q1 ^ ((m ^ 2).factorization q1) *
          q2 ^ ((m ^ 2).factorization q2) *
          q3 ^ ((m ^ 2).factorization q3) *
          q4 ^ ((m ^ 2).factorization q4)) := by
        exact OddPerfectNumber.four_support_local_product_upper
          (S q1) (S q2) (S q3) (S q4)
          (q1 ^ ((m ^ 2).factorization q1))
          (q2 ^ ((m ^ 2).factorization q2))
          (q3 ^ ((m ^ 2).factorization q3))
          (q4 ^ ((m ^ 2).factorization q4)) hi1 hi2 hi3 hi4
      _ = 5005 * m ^ 2 := by
        exact congrArg (fun z : Nat => 5005 * z) hfac.symm
  let D := (p + 1) / 2
  have hDprod : m ^ 2 = D * d := by simpa [D] using hprod
  have hpD : p = 2 * D - 1 := by
    dsimp [D]
    omega
  have hp5 : 5 ≤ p := by
    have hp2 : 2 ≤ p := hp.two_le
    by_contra h
    have hple : p ≤ 4 := by omega
    interval_cases p <;> norm_num at hp4
  have hD3 : 3 ≤ D := by dsimp [D]; omega
  have hDne3 : D ≠ 3 := by
    intro hD3eq
    have h3sq : 3 ∣ m ^ 2 := by rw [hDprod, hD3eq]; exact dvd_mul_right 3 d
    exact h3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3sq)
  have hD5 : 5 ≤ D := by
    by_contra hD
    have hDle : D ≤ 4 := by omega
    have hDcases : D = 3 ∨ D = 4 := by omega
    rcases hDcases with hD3eq | hD4eq
    · exact hDne3 hD3eq
    · have h4sq : 4 ∣ m ^ 2 := by
        rw [hDprod, hD4eq]
        exact dvd_mul_right 4 d
      obtain ⟨u, hu⟩ := h4sq
      obtain ⟨v, hv⟩ := hm2odd
      omega
  have hcoef : 9 * D ≤ 5 * p := by omega
  have hscaled : 9 * m ^ 2 ≤ 5 * (∑ x ∈ (m ^ 2).divisors, x) := by
    calc
      9 * m ^ 2 = (9 * D) * d := by rw [hDprod]; ring
      _ ≤ (5 * p) * d := Nat.mul_le_mul_right d hcoef
      _ = 5 * (p * d) := by ring
      _ = 5 * (∑ x ∈ (m ^ 2).divisors, x) := by rw [hsig]
  have hlower : 5184 * m ^ 2 ≤ 2880 * (∑ x ∈ (m ^ 2).divisors, x) := by
    calc
      5184 * m ^ 2 = 576 * (9 * m ^ 2) := by ring
      _ ≤ 576 * (5 * (∑ x ∈ (m ^ 2).divisors, x)) :=
        Nat.mul_le_mul_left 576 hscaled
      _ = 2880 * (∑ x ∈ (m ^ 2).divisors, x) := by ring
  exact OddPerfectNumber.four_support_scaled_abundance_contradiction
    (∑ x ∈ (m ^ 2).divisors, x) (m ^ 2) hupper hlower
