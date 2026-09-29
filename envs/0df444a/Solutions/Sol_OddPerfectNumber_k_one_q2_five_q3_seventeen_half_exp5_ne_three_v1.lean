-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp5_ne_three_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-20T00:14:46.339372+00:00
-- url     : https://prove2.me/submissions/e12c874d-bafa-4e1d-99a2-a7e605c9e170

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_seventeen_ge_two
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_b_three_forces_q4_19531_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp3_ge_four_or_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp17_ge_three_or_cases_v1

open OddPerfectNumber

-- `OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp5_ne_three_v1`
--
-- In the canonical q2=5, q3=17 coordinates the 5-half-exponent cannot be 3.
--
-- `b = 3` forces `q4 = 19531` (accepted `..._b_three_forces_q4_19531_v1`), and
-- `q4 = 19531` is neither `1093` nor `547`, so `..._half_exp3_ge_four_or_cases_v1`
-- gives `4 <= a`; likewise `q4 = 19531` is not `307`, `88741` or `44371`, so
-- `..._half_exp17_ge_three_or_cases_v1` gives `3 <= c`.
--
-- With `D := (p+1)/2` the Euler relation `D * sigma = p * m^2` makes the branch a
-- pure ratio statement `sigma/m^2 = (2D-1)/D`, and the four-factor identity for
-- `sigma` gives
--
--   L := (9841/6561) * (19531/15625) * (307/289) <= (2D-1)/D,
--    (2D-1)/D <= (3/2)(5/4)(17/16)(19531/19530),
--
-- using `9841/6561` (accepted `geom_ratio_lower_three_ge_eight` at `2a >= 8`),
-- the exact value `sigma(5^6) = 19531 = (5^7-1)/4` (valid because `b = 3`),
-- `307/289` (accepted `geom_ratio_lower_seventeen_ge_two`) and dropping the
-- `q4`-factor (every local ratio is `> 1`).  Cross-multiplying and cancelling
-- `m^2 > 0` gives `128 * 19530 * (2D-1) < 255 * 19531 * D` and
-- `9841 * 19531 * 307 * D <= 6561 * 15625 * 289 * (2D-1)`, i.e. `120 <= D <= 129`.
--
-- Finally `D | m^2` (from `hprod`), and every prime factor of `m` lies in
-- `{3,5,17,19531}`.  Testing `D = 120,122,124,126,128` gives `2 | m^2` (against
-- `hm : Odd m`); `D = 123,125,127` gives `2D-1 = 245,249,253` composite (against
-- `hp`); `D = 121 = 11^2` gives `11 | m^2` and `D = 129 = 3 * 43` gives
-- `43 | m^2`, both impossible because `11` and `43` are not `3`, `5`, `17` or
-- `q4 = 19531`.

set_option maxHeartbeats 2000000 in
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
    b ≠ 3 := by
  intro hb3
  obtain ⟨D, hDdef⟩ : ∃ D : Nat, D = (p + 1) / 2 := ⟨_, rfl⟩
  have hprodD : m ^ 2 = D * d := by rw [hDdef]; exact hprod
  have hq4eq : q4 = 19531 := by
    rcases k_one_q2_five_q3_seventeen_b_three_forces_q4_19531_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he with h | h
    · exact absurd hb3 h
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
  have hDdvd : D ∣ m ^ 2 := ⟨d, hprodD⟩
  have hp2 : p = 2 * D - 1 := by omega
  have hrel : D * sigma = p * m ^ 2 := by
    have h1 : sigma = p * d := by rw [hglobal, hsig]
    rw [h1, hprodD]
    ring
  have hm2pos : 0 < m ^ 2 := by rw [hfac]; positivity
  have hDpos : 0 < D := by omega
  have e3 : 9841 * 3 ^ (2*a) ≤ 6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) :=
    geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have e5 : 19531 * 5 ^ (2*b) = 15625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) := by
    rw [hb3]
    norm_num
  have e17 : 307 * 17 ^ (2*c) ≤ 289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) :=
    geom_ratio_lower_seventeen_ge_two (2*c) (by omega)
  have eq4 : q4 ^ (2*e) ≤ (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hlo : 9841 * 19531 * 307 * m ^ 2 ≤ 6561 * 15625 * 289 * sigma := by
    have s1 : (9841 * 3 ^ (2*a)) * (19531 * 5 ^ (2*b)) ≤
        (6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (15625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)) :=
      Nat.mul_le_mul e3 (le_of_eq e5)
    have s2 : ((9841 * 3 ^ (2*a)) * (19531 * 5 ^ (2*b))) * (307 * 17 ^ (2*c)) ≤
        ((6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (15625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
        (289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i)) :=
      Nat.mul_le_mul s1 e17
    have s3 : (((9841 * 3 ^ (2*a)) * (19531 * 5 ^ (2*b))) * (307 * 17 ^ (2*c))) *
        (q4 ^ (2*e)) ≤
        (((6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (15625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
        (289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))) *
        (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) :=
      Nat.mul_le_mul s2 eq4
    rw [hfac, hsigma]
    convert s3 using 1 <;> ring
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
    rw [Nat.sub_add_cancel (by omega : 1 ≤ q4)] at h
    rw [mul_comm (q4 - 1) _]
    exact h
  have f1 : 2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) < 3 ^ (2*a + 1) := by omega
  have f2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) < 5 ^ (2*b + 1) := by omega
  have f3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) < 17 ^ (2*c + 1) := by omega
  have f4 : (q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) < q4 ^ (2*e + 1) := by omega
  have l2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) ≤ 5 ^ (2*b + 1) := by omega
  have l3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) ≤ 17 ^ (2*c + 1) := by omega
  have l4 : (q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i) ≤ q4 ^ (2*e + 1) := by omega
  have hBpos : 0 < 5 ^ (2*b + 1) := by positivity
  have hCpos : 0 < 17 ^ (2*c + 1) := by positivity
  have hEpos : 0 < q4 ^ (2*e + 1) := by positivity
  have p1 : (2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))
      < 3 ^ (2*a + 1) * 5 ^ (2*b + 1) :=
    Nat.mul_lt_mul_of_lt_of_le f1 l2 hBpos
  have p2 : ((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)))
        * (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))
      < (3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1) :=
    Nat.mul_lt_mul_of_lt_of_le p1 l3 hCpos
  have p3 : (((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) * (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)))
        * (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))) * ((q4 - 1) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
      < ((3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1)) * q4 ^ (2*e + 1) :=
    Nat.mul_lt_mul_of_lt_of_le p2 l4 hEpos
  have r3 : (3 : ℕ) ^ (2*a + 1) = 3 ^ (2*a) * 3 := pow_succ 3 (2*a)
  have r5 : (5 : ℕ) ^ (2*b + 1) = 5 ^ (2*b) * 5 := pow_succ 5 (2*b)
  have r17 : (17 : ℕ) ^ (2*c + 1) = 17 ^ (2*c) * 17 := pow_succ 17 (2*c)
  have rq : q4 ^ (2*e + 1) = q4 ^ (2*e) * q4 := pow_succ q4 (2*e)
  have p3b := p3
  rw [r3, r5, r17, rq] at p3b
  have hup : 128 * (q4 - 1) * sigma < 255 * q4 * m ^ 2 := by
    rw [hsigma, hfac]
    linear_combination p3b
  have hA : 128 * (q4 - 1) * p < 255 * q4 * D := by
    have h1 := Nat.mul_lt_mul_of_pos_right hup hDpos
    have h2 : (128 * (q4 - 1) * sigma) * D =
        128 * (q4 - 1) * (p * m ^ 2) := by
      linear_combination 128 * (q4 - 1) * hrel
    rw [h2] at h1
    have h3 : (255 * q4 * m ^ 2) * D = (255 * q4 * D) * m ^ 2 := by ring
    rw [h3] at h1
    have h4 : (128 * (q4 - 1) * p) * m ^ 2 <
        (255 * q4 * D) * m ^ 2 := by
      nlinarith [h1]
    exact lt_of_mul_lt_mul_right h4 (le_of_lt hm2pos)
  have hB : 9841 * 19531 * 307 * D ≤ 6561 * 15625 * 289 * p := by
    have h1 := Nat.mul_le_mul_right D hlo
    have h2 : (6561 * 15625 * 289 * sigma) * D =
        6561 * 15625 * 289 * (p * m ^ 2) := by
      linear_combination 6561 * 15625 * 289 * hrel
    rw [h2] at h1
    have h3 : (9841 * 19531 * 307 * m ^ 2) * D =
        (9841 * 19531 * 307 * D) * m ^ 2 := by ring
    rw [h3] at h1
    have h4 : (9841 * 19531 * 307 * D) * m ^ 2 ≤
        (6561 * 15625 * 289 * p) * m ^ 2 := by
      nlinarith [h1]
    exact Nat.le_of_mul_le_mul_right h4 hm2pos
  have hDle : D ≤ 129 := by
    rw [hq4eq, hp2] at hA
    omega
  have hDge : 120 ≤ D := by
    rw [hp2] at hB
    omega
  have hkill : ∀ r : Nat, Nat.Prime r → r ∣ m ^ 2 → ¬ r ∣ 3 → ¬ r ∣ 5 →
      ¬ r ∣ 17 → ¬ r ∣ 19531 → False := by
    intro r hrp hr2 h3 h5 h17 hq
    have hnot : ¬ r ∣ 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * 19531 ^ (2*e) := by
      intro hd
      rcases hrp.dvd_mul.mp hd with hd | hd
      · rcases hrp.dvd_mul.mp hd with hd | hd
        · rcases hrp.dvd_mul.mp hd with hd | hd
          · exact h3 (hrp.dvd_of_dvd_pow hd)
          · exact h5 (hrp.dvd_of_dvd_pow hd)
        · exact h17 (hrp.dvd_of_dvd_pow hd)
      · exact hq (hrp.dvd_of_dvd_pow hd)
    exact hnot (by rw [← hq4eq, ← hfac]; exact hr2)
  by_cases h2d : (2 : Nat) ∣ D
  · have h2m : (2 : Nat) ∣ m ^ 2 := dvd_trans h2d hDdvd
    have h2m' : (2 : Nat) ∣ m := (by norm_num : Nat.Prime 2).dvd_of_dvd_pow h2m
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2m')
  · interval_cases D
    · exact absurd (by norm_num : (2 : Nat) ∣ 120) h2d
    · have h11 : (11 : Nat) ∣ m ^ 2 :=
        dvd_trans (by norm_num : (11 : Nat) ∣ 121) hDdvd
      exact hkill 11 (by norm_num) h11
        (by norm_num : ¬ (11 : Nat) ∣ 3) (by norm_num : ¬ (11 : Nat) ∣ 5)
        (by norm_num : ¬ (11 : Nat) ∣ 17) (by norm_num : ¬ (11 : Nat) ∣ 19531)
    · exact absurd (by norm_num : (2 : Nat) ∣ 122) h2d
    · exact absurd hp (by rw [hp2]; norm_num)
    · exact absurd (by norm_num : (2 : Nat) ∣ 124) h2d
    · exact absurd hp (by rw [hp2]; norm_num)
    · exact absurd (by norm_num : (2 : Nat) ∣ 126) h2d
    · exact absurd hp (by rw [hp2]; norm_num)
    · exact absurd (by norm_num : (2 : Nat) ∣ 128) h2d
    · have h43 : (43 : Nat) ∣ m ^ 2 :=
        dvd_trans (by norm_num : (43 : Nat) ∣ 129) hDdvd
      exact hkill 43 (by norm_num) h43
        (by norm_num : ¬ (43 : Nat) ∣ 3) (by norm_num : ¬ (43 : Nat) ∣ 5)
        (by norm_num : ¬ (43 : Nat) ∣ 17) (by norm_num : ¬ (43 : Nat) ∣ 19531)
