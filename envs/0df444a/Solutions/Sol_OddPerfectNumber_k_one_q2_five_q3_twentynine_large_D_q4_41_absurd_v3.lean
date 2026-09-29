-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T10:10:53.834768+00:00
-- url     : https://prove2.me/submissions/f51114a2-678f-4cd2-91f4-85ede4196c1b

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hDupper : D ≤ 105) (hDodd : Odd D) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4eq : q4 = 41)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : False := by
  have hDcases : D = 75 ∨ D = 79 ∨ D = 87 ∨ D = 91 ∨ D = 97 ∨ D = 99 := by
    have hsplit : D ≤ 89 ∨ 90 ≤ D := by omega
    rcases hsplit with hsmall | hlarge
    · interval_cases D <;> norm_num [hp_eq] at hDodd <;>
        norm_num [hp_eq] at hp <;> norm_num <;> omega
    · interval_cases D <;> norm_num [hp_eq] at hDodd <;>
        norm_num [hp_eq] at hp <;> norm_num <;> omega
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hlast29 := OddPerfectNumber.geom_sum_last_three_terms_le 29 (2*c) (by omega)
  have hlastq := OddPerfectNumber.geom_sum_last_three_terms_le 41 (2*e) (by omega)
  have hpow29a : 29 ^ (2*c) = 29 ^ (2*c - 2) * 841 := by
    calc
      29 ^ (2*c) = 29 ^ ((2*c - 2) + 2) := by congr 1 <;> omega
      _ = 29 ^ (2*c - 2) * 29^2 := by rw [pow_add]
      _ = 29 ^ (2*c - 2) * 841 := by norm_num
  have hpow29b : 29 ^ (2*c - 1) = 29 ^ (2*c - 2) * 29 := by
    calc
      29 ^ (2*c - 1) = 29 ^ ((2*c - 2) + 1) := by congr 1 <;> omega
      _ = 29 ^ (2*c - 2) * 29 := by rw [pow_succ]
  have hpowq_a : 41 ^ (2*e) = 41 ^ (2*e - 2) * 1681 := by
    calc
      41 ^ (2*e) = 41 ^ ((2*e - 2) + 2) := by congr 1 <;> omega
      _ = 41 ^ (2*e - 2) * 41^2 := by rw [pow_add]
      _ = 41 ^ (2*e - 2) * 1681 := by norm_num
  have hpowq_b : 41 ^ (2*e - 1) = 41 ^ (2*e - 2) * 41 := by
    calc
      41 ^ (2*e - 1) = 41 ^ ((2*e - 2) + 1) := by congr 1 <;> omega
      _ = 41 ^ (2*e - 2) * 41 := by rw [pow_succ]
  have h29 : 871 * 29 ^ (2*c) ≤ 841 * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) := by
    nlinarith [hlast29, hpow29a, hpow29b]
  have hq : 1723 * 41 ^ (2*e) ≤ 1681 * (∑ i ∈ Finset.range (2*e + 1), 41 ^ i) := by
    nlinarith [hlastq, hpowq_a, hpowq_b]
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) (Nat.mul_le_mul h29 hq)
  have hcross :
      288447742450543 * (3^(2*a) * 5^(2*b) * 29^(2*c) * 41^(2*e)) ≤
        144928491890625 *
          ((∑ i ∈ Finset.range (2*a + 1), 3^i) *
           (∑ i ∈ Finset.range (2*b + 1), 5^i) *
           (∑ i ∈ Finset.range (2*c + 1), 29^i) *
           (∑ i ∈ Finset.range (2*e + 1), 41^i)) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    simpa [hq4eq] using
      (show 0 < 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * 41 ^ (2*e) by positivity)
  have hfac41 : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * 41 ^ (2*e) := by
    simpa [hq4eq] using hfac
  have hsigma41 : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3^i) *
      (∑ i ∈ Finset.range (2*b + 1), 5^i) *
      (∑ i ∈ Finset.range (2*c + 1), 29^i) *
      (∑ i ∈ Finset.range (2*e + 1), 41^i) := by
    simpa [hq4eq] using hsigma
  rcases hDcases with h75 | h79 | h87 | h91 | h97 | h99
  · have hineq : 288447742450543 * 75 * (m^2) ≤ 144928491890625 * 149 * (m^2) := by
      have hmulD := Nat.mul_le_mul_left 75 hcross
      calc
        288447742450543 * 75 * (m^2) =
            75 * (288447742450543 *
              (3^(2*a) * 5^(2*b) * 29^(2*c) * 41^(2*e))) := by
                rw [hfac41]
                ring
        _ ≤ 75 * (144928491890625 *
            ((∑ i ∈ Finset.range (2*a + 1), 3^i) *
             (∑ i ∈ Finset.range (2*b + 1), 5^i) *
             (∑ i ∈ Finset.range (2*c + 1), 29^i) *
             (∑ i ∈ Finset.range (2*e + 1), 41^i))) := by
                simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmulD
        _ = 144928491890625 * (75 * sigma) := by
                rw [hsigma41]
                ring
        _ = 144928491890625 * (149 * m^2) := by
                have hrel75 : 75 * sigma = 149 * m^2 := by
                  simpa [h75, hp_eq] using hrel
                rw [hrel75]
        _ = 144928491890625 * 149 * (m^2) := by ring
    have hcancel : 288447742450543 * 75 ≤ 144928491890625 * 149 :=
      Nat.le_of_mul_le_mul_right hineq hmpos
    norm_num at hcancel
  · have h := hDsupport 79 (by norm_num) (by simpa [h79])
    norm_num at h
    omega
  · have hineq : 288447742450543 * 87 * (m^2) ≤ 144928491890625 * 173 * (m^2) := by
      have hmulD := Nat.mul_le_mul_left 87 hcross
      calc
        288447742450543 * 87 * (m^2) =
            87 * (288447742450543 *
              (3^(2*a) * 5^(2*b) * 29^(2*c) * 41^(2*e))) := by
                rw [hfac41]
                ring
        _ ≤ 87 * (144928491890625 *
            ((∑ i ∈ Finset.range (2*a + 1), 3^i) *
             (∑ i ∈ Finset.range (2*b + 1), 5^i) *
             (∑ i ∈ Finset.range (2*c + 1), 29^i) *
             (∑ i ∈ Finset.range (2*e + 1), 41^i))) := by
                simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmulD
        _ = 144928491890625 * (87 * sigma) := by
                rw [hsigma41]
                ring
        _ = 144928491890625 * (173 * m^2) := by
                have hrel87 : 87 * sigma = 173 * m^2 := by
                  simpa [h87, hp_eq] using hrel
                rw [hrel87]
        _ = 144928491890625 * 173 * (m^2) := by ring
    have hcancel : 288447742450543 * 87 ≤ 144928491890625 * 173 :=
      Nat.le_of_mul_le_mul_right hineq hmpos
    norm_num at hcancel
  · have h := hDsupport 7 (by norm_num) (by simpa [h91])
    norm_num at h
    omega
  · have h := hDsupport 97 (by norm_num) (by simpa [h97])
    norm_num at h
    omega
  · have h := hDsupport 11 (by norm_num) (by simpa [h99])
    norm_num at h
    omega
