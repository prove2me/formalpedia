-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_abundance_absurd_v5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T00:42:16.741385+00:00
-- url     : https://prove2.me/submissions/d935d286-6f90-4618-8be3-c709b21ac5e6

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_force_three_source_v9
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_ten
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_263_ge_two

theorem solution (m a b c e sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2 * a) * 5 ^ (2 * b) * 19 ^ (2 * c) * 263 ^ (2 * e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i))
    (hrel : 75 * sigma = 149 * m ^ 2)
    (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  let S3 := ∑ i ∈ Finset.range (2 * a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2 * b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (2 * c + 1), 19 ^ i
  let S263 := ∑ i ∈ Finset.range (2 * e + 1), 263 ^ i
  have hpow : 263 ∣ 263 ^ (2 * e) := dvd_pow_self 263 (by omega)
  have hmdiv : 263 ∣ m ^ 2 := by
    rw [hfac]
    exact dvd_mul_of_dvd_right hpow _
  have hmuldiv : 263 ∣ 75 * sigma := by
    rw [hrel]
    exact dvd_mul_of_dvd_right hmdiv 149
  have hdiv : 263 ∣ sigma := by
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 263)).mp hmuldiv with h | h
    · norm_num at h
    · exact h
  have hsource := OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_force_three_source_v9
    sigma a b c e hsigma hdiv
  have h3 : 88573 * 3 ^ (2 * a) ≤ 59049 * S3 := by
    simpa [S3] using
      OddPerfectNumber.geom_ratio_lower_three_ge_ten (2 * a) (by omega)
  have h5 : 19531 * 5 ^ (2 * b) ≤ 15625 * S5 := by
    simpa [S5] using
      OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2 * b) (by omega)
  have h19 : 137561 * 19 ^ (2 * c) ≤ 130321 * S19 := by
    simpa [S19] using
      OddPerfectNumber.geom_ratio_lower_nineteen_ge_four (2 * c) (by omega)
  have h263 : 69433 * 263 ^ (2 * e) ≤ 69169 * S263 := by
    simpa [S263] using
      OddPerfectNumber.geom_ratio_lower_263_ge_two (2 * e) (by omega)
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul19q := Nat.mul_le_mul h19 h263
  have hmul := Nat.mul_le_mul hmul35 hmul19q
  have hcross :
      16522930998368823119 *
          (3 ^ (2 * a) * 5 ^ (2 * b) * 19 ^ (2 * c) * 263 ^ (2 * e)) ≤
        8316842440315640625 * (S3 * S5 * S19 * S263) := by
    calc
      16522930998368823119 *
          (3 ^ (2 * a) * 5 ^ (2 * b) * 19 ^ (2 * c) * 263 ^ (2 * e)) =
          (88573 * 3 ^ (2 * a)) * (19531 * 5 ^ (2 * b)) *
            ((137561 * 19 ^ (2 * c)) * (69433 * 263 ^ (2 * e))) := by ring
      _ ≤ (59049 * S3) * (15625 * S5) *
            ((130321 * S19) * (69169 * S263)) := by
            simpa only [S3, S5, S19, S263] using hmul
      _ = 8316842440315640625 * (S3 * S5 * S19 * S263) := by ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hineq :
      16522930998368823119 * 75 * (m ^ 2) ≤
        8316842440315640625 * 149 * (m ^ 2) := by
    have hmulD := Nat.mul_le_mul_left 75 hcross
    calc
      16522930998368823119 * 75 * (m ^ 2) =
          75 * (16522930998368823119 * (m ^ 2)) := by ring
      _ = 75 * (16522930998368823119 *
            (3 ^ (2 * a) * 5 ^ (2 * b) * 19 ^ (2 * c) * 263 ^ (2 * e))) := by rw [hfac]
      _ ≤ 75 * (8316842440315640625 * (S3 * S5 * S19 * S263)) := hmulD
      _ = 8316842440315640625 * 75 * sigma := by rw [hsigma]; ring
      _ = 8316842440315640625 * (75 * sigma) := by ring
      _ = 8316842440315640625 * (149 * (m ^ 2)) := by rw [hrel]
      _ = 8316842440315640625 * 149 * (m ^ 2) := by ring
  have hconst :
      8316842440315640625 * 149 < 16522930998368823119 * 75 := by norm_num
  have hstrict :
      8316842440315640625 * 149 * (m ^ 2) <
        16522930998368823119 * 75 * (m ^ 2) := by
    exact Nat.mul_lt_mul_of_pos_right hconst hmpos
  exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
