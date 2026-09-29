-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_a_three_forces_q4_547_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-20T00:59:10.026833+00:00
-- url     : https://prove2.me/submissions/c1c4a9c7-5c3e-4456-8718-292b36e6f60f

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_seventeen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_a_three_forces_q4_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp5_ge_four_or_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp17_ge_three_or_cases_v1

open OddPerfectNumber

-- `OddPerfectNumber.k_one_q2_five_q3_seventeen_a_three_forces_q4_547_v1`
--
-- In the canonical q2=5, q3=17 coordinates, 3-half-exponent 3 forces the fourth
-- prime to be 547:  `a != 3 or q4 = 547`.
--
-- `a = 3` gives `q4 = 1093 or q4 = 547`
-- (accepted `..._a_three_forces_q4_cases_v1`).  In the `q4 = 1093` branch the
-- 3-component is exactly `sigma(3^6) = 1093`, and with `4 <= b`, `3 <= c` the
-- ratio `sigma/m^2 = (2D-1)/D` (for `D = (p+1)/2`) is squeezed into
-- `137 <= D <= 166`:
--
--   lower: `1093 * 488281 * 307 * 1094 * D <= 729 * 390625 * 289 * 1093 * p`,
--   upper: `128 * 1092 * p < 255 * 1093 * D`,
--
-- using the exact `sigma(3^6) = 1093`, the sharp `sigma(5^8)/5^8 >= 488281/390625`
-- (valid because `2b >= 8`), `geom_ratio_lower_seventeen_ge_two` and the top-two
-- terms `sigma(1093^2)/1093^2 >= 1094/1093` of the fourth component.
--
-- Then `D | m^2` and `D` in that window are enumerated: the even values force
-- `2 | m`, `153 = 9 * 17` makes `2D-1 = 305` composite, and every remaining value
-- has a prime factor outside the support `{3, 5, 17, 1093}`.  So the
-- `q4 = 1093` branch is impossible and only `q4 = 547` survives.

set_option maxHeartbeats 3000000 in
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
    a ≠ 3 ∨ q4 = 547 := by
  by_cases ha3 : a = 3
  · rcases k_one_q2_five_q3_seventeen_a_three_forces_q4_cases_v1 p m d q4 a b c e sigma
      hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
      h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he with h | h | h
    · exact absurd ha3 h
    · exfalso
      have hq4v : q4 = 1093 := h
      have hb4 : 4 ≤ b := by
        rcases k_one_q2_five_q3_seventeen_half_exp5_ge_four_or_cases_v1 p m d q4 a b c e sigma
          hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
          h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he with h' | h' | h'
        · exact h'
        · omega
        · omega
      have hc3 : 3 ≤ c := by
        rcases k_one_q2_five_q3_seventeen_half_exp17_ge_three_or_cases_v1 p m d q4 a b c e sigma
          hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt hfac hsigma hglobal
          h3mem h3exp h5mem h5exp h17mem h17exp ha hb hc he with h' | h' | h' | h'
        · exact h'
        · omega
        · omega
        · omega
      obtain ⟨D, hDdef⟩ : ∃ D : Nat, D = (p + 1) / 2 := ⟨_, rfl⟩
      have hprodD : m ^ 2 = D * d := by rw [hDdef]; exact hprod
      have hp2 : p = 2 * D - 1 := by omega
      have hm2pos : 0 < m ^ 2 := by rw [hfac]; positivity
      have hDpos : 0 < D := by omega
      have hDdvd : D ∣ m ^ 2 := ⟨d, hprodD⟩
      have hrel : D * sigma = p * m ^ 2 := by
        have h1 : sigma = p * d := by rw [hglobal, hsig]
        rw [h1, hprodD]
        ring
      have e3 : 1093 * 3 ^ (2*a) = 729 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) := by
        rw [ha3]
        norm_num
      have e5 : 488281 * 5 ^ (2*b) ≤ 390625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) := by
        have h4 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) + 1 = 5 ^ (2*b + 1) := by
          rw [mul_comm 4 _]
          exact geom_sum_mul_add 4 (2*b + 1)
        have h8 : (390625 : Nat) ≤ 5 ^ (2*b) := by
          simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 5) (by omega : 8 ≤ 2*b)
        have h51 : (5 : Nat) ^ (2*b + 1) = 5 * 5 ^ (2*b) := pow_succ' 5 (2*b)
        omega
      have e17 : 307 * 17 ^ (2*c) ≤ 289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) :=
        geom_ratio_lower_seventeen_ge_two (2*c) (by omega)
      have hsplitq : (∑ i ∈ Finset.range (2*e + 1), 1093 ^ i) =
          (∑ i ∈ Finset.range (2*e), 1093 ^ i) + 1093 ^ (2*e) := by
        rw [Finset.sum_range_succ]
      have hlowq : 1093 ^ (2*e - 1) ≤ ∑ i ∈ Finset.range (2*e), 1093 ^ i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      have hpowq : 1093 * 1093 ^ (2*e - 1) = 1093 ^ (2*e) := by
        rw [← pow_succ']
        congr 1
        omega
      have eqq : 1094 * 1093 ^ (2*e) ≤ 1093 * (∑ i ∈ Finset.range (2*e + 1), 1093 ^ i) := by
        rw [hsplitq]
        nlinarith [hlowq, hpowq]
      have hlo : 1093 * 488281 * 307 * 1094 * m ^ 2 ≤
          729 * 390625 * 289 * 1093 * sigma := by
        have s1 : (1093 * 3 ^ (2*a)) * (488281 * 5 ^ (2*b)) ≤
            (729 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
              (390625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)) :=
          Nat.mul_le_mul (le_of_eq e3) e5
        have s2 : ((1093 * 3 ^ (2*a)) * (488281 * 5 ^ (2*b))) * (307 * 17 ^ (2*c)) ≤
            ((729 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
              (390625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
            (289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i)) :=
          Nat.mul_le_mul s1 e17
        have s3 : (((1093 * 3 ^ (2*a)) * (488281 * 5 ^ (2*b))) * (307 * 17 ^ (2*c))) *
            (1094 * 1093 ^ (2*e)) ≤
            (((729 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
              (390625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
            (289 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))) *
            (1093 * (∑ i ∈ Finset.range (2*e + 1), 1093 ^ i)) :=
          Nat.mul_le_mul s2 eqq
        rw [ha3] at s3
        rw [hfac, hsigma, ha3, hq4v]
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
      have gq : (1093 - 1) * (∑ i ∈ Finset.range (2*e + 1), 1093 ^ i) + 1 =
          1093 ^ (2*e + 1) := by
        have h := geom_sum_mul_add (1093 - 1) (2*e + 1)
        rw [Nat.sub_add_cancel (by norm_num : 1 ≤ 1093)] at h
        rw [mul_comm (1093 - 1) _]
        exact h
      have f1 : 2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) < 3 ^ (2*a + 1) := by omega
      have f2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) < 5 ^ (2*b + 1) := by omega
      have f3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) < 17 ^ (2*c + 1) := by omega
      have f4 : (1093 - 1) * (∑ i ∈ Finset.range (2*e + 1), 1093 ^ i) <
          1093 ^ (2*e + 1) := by omega
      have l2 : 4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) ≤ 5 ^ (2*b + 1) := by omega
      have l3 : 16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) ≤ 17 ^ (2*c + 1) := by omega
      have l4 : (1093 - 1) * (∑ i ∈ Finset.range (2*e + 1), 1093 ^ i) ≤
          1093 ^ (2*e + 1) := by omega
      have hBpos : 0 < 5 ^ (2*b + 1) := by positivity
      have hCpos : 0 < 17 ^ (2*c + 1) := by positivity
      have hEpos : 0 < 1093 ^ (2*e + 1) := by positivity
      have p1 : (2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)) < 3 ^ (2*a + 1) * 5 ^ (2*b + 1) :=
        Nat.mul_lt_mul_of_lt_of_le f1 l2 hBpos
      have p2 : ((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
          (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i)) <
          (3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1) :=
        Nat.mul_lt_mul_of_lt_of_le p1 l3 hCpos
      have p3 : (((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
          (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
          (16 * (∑ i ∈ Finset.range (2*c + 1), 17 ^ i))) *
          ((1093 - 1) * (∑ i ∈ Finset.range (2*e + 1), 1093 ^ i)) <
          ((3 ^ (2*a + 1) * 5 ^ (2*b + 1)) * 17 ^ (2*c + 1)) * 1093 ^ (2*e + 1) :=
        Nat.mul_lt_mul_of_lt_of_le p2 l4 hEpos
      have r3 : (3 : Nat) ^ (2*a + 1) = 3 ^ (2*a) * 3 := pow_succ 3 (2*a)
      have r5 : (5 : Nat) ^ (2*b + 1) = 5 ^ (2*b) * 5 := pow_succ 5 (2*b)
      have r17 : (17 : Nat) ^ (2*c + 1) = 17 ^ (2*c) * 17 := pow_succ 17 (2*c)
      have rq : 1093 ^ (2*e + 1) = 1093 ^ (2*e) * 1093 := pow_succ 1093 (2*e)
      have p3b := p3
      rw [r3, r5, r17, rq] at p3b
      have hup : 128 * (1093 - 1) * sigma < 255 * 1093 * m ^ 2 := by
        rw [hsigma, hfac, hq4v]
        linear_combination p3b
      have hA : 128 * (1093 - 1) * p < 255 * 1093 * D := by
        have h1 := Nat.mul_lt_mul_of_pos_right hup hDpos
        have h2 : (128 * (1093 - 1) * sigma) * D = 128 * (1093 - 1) * (p * m ^ 2) := by
          linear_combination 128 * (1093 - 1) * hrel
        rw [h2] at h1
        have h3 : (255 * 1093 * m ^ 2) * D = (255 * 1093 * D) * m ^ 2 := by ring
        rw [h3] at h1
        have h4 : (128 * (1093 - 1) * p) * m ^ 2 < (255 * 1093 * D) * m ^ 2 := by
          nlinarith [h1]
        exact lt_of_mul_lt_mul_right h4 (le_of_lt hm2pos)
      have hB : 1093 * 488281 * 307 * 1094 * D ≤ 729 * 390625 * 289 * 1093 * p := by
        have h1 := Nat.mul_le_mul_right D hlo
        have h2 : (729 * 390625 * 289 * 1093 * sigma) * D =
            729 * 390625 * 289 * 1093 * (p * m ^ 2) := by
          linear_combination 729 * 390625 * 289 * 1093 * hrel
        rw [h2] at h1
        have h3 : (1093 * 488281 * 307 * 1094 * m ^ 2) * D =
            (1093 * 488281 * 307 * 1094 * D) * m ^ 2 := by ring
        rw [h3] at h1
        have h4 : (1093 * 488281 * 307 * 1094 * D) * m ^ 2 ≤
            (729 * 390625 * 289 * 1093 * p) * m ^ 2 := by
          nlinarith [h1]
        exact Nat.le_of_mul_le_mul_right h4 hm2pos
      have hDle : D ≤ 166 := by
        rw [hp2] at hA
        omega
      have hDge : 137 ≤ D := by
        rw [hp2] at hB
        omega
      by_cases h2d : (2 : Nat) ∣ D
      · have h2m : (2 : Nat) ∣ m ^ 2 := dvd_trans h2d hDdvd
        have h2m' : (2 : Nat) ∣ m := (by norm_num : Nat.Prime 2).dvd_of_dvd_pow h2m
        exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2m')
      · have hkill : ∀ r : Nat, Nat.Prime r → r ∣ m ^ 2 → ¬ r ∣ 3 → ¬ r ∣ 5 →
            ¬ r ∣ 17 → ¬ r ∣ 1093 → False := by
          intro r hrp hr2 h3 h5 h17 hq
          have hnot : ¬ r ∣ 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * 1093 ^ (2*e) := by
            intro hd
            rcases hrp.dvd_mul.mp hd with hd | hd
            · rcases hrp.dvd_mul.mp hd with hd | hd
              · rcases hrp.dvd_mul.mp hd with hd | hd
                · exact h3 (hrp.dvd_of_dvd_pow hd)
                · exact h5 (hrp.dvd_of_dvd_pow hd)
              · exact h17 (hrp.dvd_of_dvd_pow hd)
            · exact hq (hrp.dvd_of_dvd_pow hd)
          exact hnot (by rw [← hq4v, ← hfac]; exact hr2)
        interval_cases D
        · exact hkill 137 (by norm_num) (dvd_trans (by norm_num : (137 : Nat) ∣ 137) hDdvd) (by norm_num : ¬ (137 : Nat) ∣ 3) (by norm_num : ¬ (137 : Nat) ∣ 5) (by norm_num : ¬ (137 : Nat) ∣ 17) (by norm_num : ¬ (137 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 138) h2d
        · exact hkill 139 (by norm_num) (dvd_trans (by norm_num : (139 : Nat) ∣ 139) hDdvd) (by norm_num : ¬ (139 : Nat) ∣ 3) (by norm_num : ¬ (139 : Nat) ∣ 5) (by norm_num : ¬ (139 : Nat) ∣ 17) (by norm_num : ¬ (139 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 140) h2d
        · exact hkill 47 (by norm_num) (dvd_trans (by norm_num : (47 : Nat) ∣ 141) hDdvd) (by norm_num : ¬ (47 : Nat) ∣ 3) (by norm_num : ¬ (47 : Nat) ∣ 5) (by norm_num : ¬ (47 : Nat) ∣ 17) (by norm_num : ¬ (47 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 142) h2d
        · exact hkill 11 (by norm_num) (dvd_trans (by norm_num : (11 : Nat) ∣ 143) hDdvd) (by norm_num : ¬ (11 : Nat) ∣ 3) (by norm_num : ¬ (11 : Nat) ∣ 5) (by norm_num : ¬ (11 : Nat) ∣ 17) (by norm_num : ¬ (11 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 144) h2d
        · exact hkill 29 (by norm_num) (dvd_trans (by norm_num : (29 : Nat) ∣ 145) hDdvd) (by norm_num : ¬ (29 : Nat) ∣ 3) (by norm_num : ¬ (29 : Nat) ∣ 5) (by norm_num : ¬ (29 : Nat) ∣ 17) (by norm_num : ¬ (29 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 146) h2d
        · exact hkill 7 (by norm_num) (dvd_trans (by norm_num : (7 : Nat) ∣ 147) hDdvd) (by norm_num : ¬ (7 : Nat) ∣ 3) (by norm_num : ¬ (7 : Nat) ∣ 5) (by norm_num : ¬ (7 : Nat) ∣ 17) (by norm_num : ¬ (7 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 148) h2d
        · exact hkill 149 (by norm_num) (dvd_trans (by norm_num : (149 : Nat) ∣ 149) hDdvd) (by norm_num : ¬ (149 : Nat) ∣ 3) (by norm_num : ¬ (149 : Nat) ∣ 5) (by norm_num : ¬ (149 : Nat) ∣ 17) (by norm_num : ¬ (149 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 150) h2d
        · exact hkill 151 (by norm_num) (dvd_trans (by norm_num : (151 : Nat) ∣ 151) hDdvd) (by norm_num : ¬ (151 : Nat) ∣ 3) (by norm_num : ¬ (151 : Nat) ∣ 5) (by norm_num : ¬ (151 : Nat) ∣ 17) (by norm_num : ¬ (151 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 152) h2d
        · exact absurd hp (by rw [hp2]; norm_num)
        · exact absurd (by norm_num : (2 : Nat) ∣ 154) h2d
        · exact hkill 31 (by norm_num) (dvd_trans (by norm_num : (31 : Nat) ∣ 155) hDdvd) (by norm_num : ¬ (31 : Nat) ∣ 3) (by norm_num : ¬ (31 : Nat) ∣ 5) (by norm_num : ¬ (31 : Nat) ∣ 17) (by norm_num : ¬ (31 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 156) h2d
        · exact hkill 157 (by norm_num) (dvd_trans (by norm_num : (157 : Nat) ∣ 157) hDdvd) (by norm_num : ¬ (157 : Nat) ∣ 3) (by norm_num : ¬ (157 : Nat) ∣ 5) (by norm_num : ¬ (157 : Nat) ∣ 17) (by norm_num : ¬ (157 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 158) h2d
        · exact hkill 53 (by norm_num) (dvd_trans (by norm_num : (53 : Nat) ∣ 159) hDdvd) (by norm_num : ¬ (53 : Nat) ∣ 3) (by norm_num : ¬ (53 : Nat) ∣ 5) (by norm_num : ¬ (53 : Nat) ∣ 17) (by norm_num : ¬ (53 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 160) h2d
        · exact hkill 7 (by norm_num) (dvd_trans (by norm_num : (7 : Nat) ∣ 161) hDdvd) (by norm_num : ¬ (7 : Nat) ∣ 3) (by norm_num : ¬ (7 : Nat) ∣ 5) (by norm_num : ¬ (7 : Nat) ∣ 17) (by norm_num : ¬ (7 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 162) h2d
        · exact hkill 163 (by norm_num) (dvd_trans (by norm_num : (163 : Nat) ∣ 163) hDdvd) (by norm_num : ¬ (163 : Nat) ∣ 3) (by norm_num : ¬ (163 : Nat) ∣ 5) (by norm_num : ¬ (163 : Nat) ∣ 17) (by norm_num : ¬ (163 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 164) h2d
        · exact hkill 11 (by norm_num) (dvd_trans (by norm_num : (11 : Nat) ∣ 165) hDdvd) (by norm_num : ¬ (11 : Nat) ∣ 3) (by norm_num : ¬ (11 : Nat) ∣ 5) (by norm_num : ¬ (11 : Nat) ∣ 17) (by norm_num : ¬ (11 : Nat) ∣ 1093)
        · exact absurd (by norm_num : (2 : Nat) ∣ 166) h2d
    · exact Or.inr h
  · exact Or.inl ha3
