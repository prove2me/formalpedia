-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp5_ne_one_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-20T00:25:28.373521+00:00
-- url     : https://prove2.me/submissions/e4b74bd7-c5b2-4d38-86db-3b570132fd8a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_seventeen_ge_two
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp5_one_forces_q4_31_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp3_ge_four_or_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp17_ge_three_or_cases_v1

open OddPerfectNumber

-- `OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp5_ne_one_v1`
--
-- In the canonical q2=5, q3=17 coordinates the 5-half-exponent cannot be 1.
--
-- `b = 1` forces `q4 = 31` (accepted `..._half_exp5_one_forces_q4_31_v1`), and
-- `q4 = 31` is neither `1093` nor `547`, so `..._half_exp3_ge_four_or_cases_v1`
-- gives `4 <= a`; likewise `q4 = 31` is not `307`, `88741` or `44371`, so
-- `..._half_exp17_ge_three_or_cases_v1` gives `3 <= c`.
--
-- With `D := (p+1)/2`, `hprod`/`hsig`/`hglobal` give `D * sigma = p * m^2`, so
-- `sigma/m^2 = (2D-1)/D < 2`.  On the other hand the four-factor identity and
-- the bounds
--
--   `9841/6561`  (`geom_ratio_lower_three_ge_eight`, `2a >= 8`),
--   `31/25`      (exact, because `b = 1`),
--   `307/289`    (`geom_ratio_lower_seventeen_ge_two`),
--   `32/31`      (`S_31(2e)/31^(2e) >= (31+1)/31`, from the top two terms)
--
-- give `sigma/m^2 >= (9841/6561) * (31/25) * (307/289) * (32/31) > 2`,
-- contradicting `sigma/m^2 < 2` (cross-multiplied:
-- `9841 * 31 * 307 * 32 * m^2 <= 6561 * 25 * 289 * 31 * sigma` together with
-- `sigma < 2 * m^2` forces `9841 * 31 * 307 * 32 < 6561 * 25 * 289 * 31 * 2`,
-- which is false).

set_option maxHeartbeats 1600000 in
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 17 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 17 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h17mem : 17 ∈ (m ^ 2).primeFactors)
    (h17exp : (m ^ 2).factorization 17 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    b ≠ 1 := by
  intro hb1
  have hq4eq : q4 = 31 := by
    rcases k_one_q2_five_q3_seventeen_half_exp5_one_forces_q4_31_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he with h | h
    · exact absurd hb1 h
    · exact h
  have ha4 : 4 ≤ a := by
    rcases k_one_q2_five_q3_seventeen_half_exp3_ge_four_or_cases_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he with h | h | h
    · exact h
    · omega
    · omega
  have hc3 : 3 ≤ c := by
    rcases k_one_q2_five_q3_seventeen_half_exp17_ge_three_or_cases_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he with h | h | h | h
    · exact h
    · omega
    · omega
    · omega
  have hm2pos : 0 < m ^ 2 := by rw [hfac]; positivity
  have hDpos : 0 < (p + 1) / 2 := by omega
  have hrel : ((p + 1) / 2) * sigma = p * m ^ 2 := by
    have h1 : sigma = p * d := by rw [hglobal, hsig]
    rw [h1, hprod]
    ring
  have e3 : 9841 * 3 ^ (2*a) ≤ 6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) :=
    geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have e5 : 31 * 5 ^ (2*b) = 25 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) := by
    rw [hb1]
    norm_num
  have e17 : 307 * 17 ^ (2*c) ≤ 289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) :=
    geom_ratio_lower_seventeen_ge_two (2*c) (by omega)
  have hsplit31 : (∑ i ∈ Finset.range (2*e + 1), 31 ^ i) =
      (∑ i ∈ Finset.range (2*e), 31 ^ i) + 31 ^ (2*e) := by
    rw [Finset.sum_range_succ]
  have hlow31 : 31 ^ (2*e - 1) ≤ ∑ i ∈ Finset.range (2*e), 31 ^ i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hpow31 : 31 * 31 ^ (2*e - 1) = 31 ^ (2*e) := by
    rw [← pow_succ']
    congr 1
    omega
  have eqq : 32 * 31 ^ (2*e) ≤ 31 * (∑ i ∈ Finset.range (2*e + 1), 31 ^ i) := by
    rw [hsplit31]
    nlinarith [hlow31, hpow31]
  have hlo : 9841 * 31 * 307 * 32 * m ^ 2 ≤ 6561 * 25 * 289 * 31 * sigma := by
    have s1 : (9841 * 3 ^ (2*a)) * (31 * 5 ^ (2*b)) ≤
        (6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (25 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)) :=
      Nat.mul_le_mul e3 (le_of_eq e5)
    have s2 : ((9841 * 3 ^ (2*a)) * (31 * 5 ^ (2*b))) * (307 * 17 ^ (2*c)) ≤
        ((6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (25 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
        (289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i)) :=
      Nat.mul_le_mul s1 e17
    have s3 : (((9841 * 3 ^ (2*a)) * (31 * 5 ^ (2*b))) * (307 * 17 ^ (2*c))) *
        (32 * 31 ^ (2*e)) ≤
        (((6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (25 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
        (289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))) *
        (31 * (∑ i ∈ Finset.range (2*e + 1), 31 ^ i)) :=
      Nat.mul_le_mul s2 eqq
    rw [hb1] at s3
    rw [hfac, hsigma, hb1, hq4eq]
    convert s3 using 1 <;> ring
  have hσlt : sigma < 2 * m ^ 2 := by
    have h1 : sigma * ((p + 1) / 2) = p * m ^ 2 := by rw [mul_comm, hrel]
    have h2 : p * m ^ 2 < (2 * m ^ 2) * ((p + 1) / 2) := by
      have hmul := Nat.mul_lt_mul_of_pos_right (by omega : p < 2 * ((p + 1) / 2)) hm2pos
      nlinarith [hmul]
    rw [← h1] at h2
    exact lt_of_mul_lt_mul_right h2 (le_of_lt hDpos)
  have hbig : (9841 * 31 * 307 * 32 * m ^ 2) <
      (6561 * 25 * 289 * 31 * (2 * m ^ 2)) :=
    lt_of_le_of_lt hlo (Nat.mul_lt_mul_of_pos_left hσlt (by positivity))
  have h4 : (9841 * 31 * 307 * 32) * m ^ 2 <
      (6561 * 25 * 289 * 31 * 2) * m ^ 2 := by
    nlinarith [hbig]
  have h5 : (9841 * 31 * 307 * 32 : Nat) < (6561 * 25 * 289 * 31 * 2 : Nat) :=
    lt_of_mul_lt_mul_right h4 (le_of_lt hm2pos)
  norm_num at h5
