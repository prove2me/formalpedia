-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T09:11:48.343805+00:00
-- url     : https://prove2.me/submissions/736d7d5d-aaf9-4758-bd14-b292b80007fd

import Mathlib

theorem solution (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4gt : 29 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) :
    D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  have hcases :
      D = 19 ∨ D = 21 ∨ D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 ∨
      D = 49 ∨ D = 51 ∨ D = 55 ∨ D = 57 ∨ D = 69 := by
    have hDlo : 16 ≤ D := by omega
    have hDhi : D ≤ 74 := by omega
    have hparts :
        D ≤ 29 ∨ (30 ≤ D ∧ D ≤ 44) ∨ (45 ≤ D ∧ D ≤ 59) ∨ 60 ≤ D := by
      omega
    rcases hparts with hpart | hpart | hpart | hpart
    · interval_cases D <;> norm_num [hp_eq] at hDodd <;>
        norm_num [hp_eq] at hp <;> norm_num <;> omega
    · interval_cases D <;> norm_num [hp_eq] at hDodd <;>
        norm_num [hp_eq] at hp <;> norm_num <;> omega
    · interval_cases D <;> norm_num [hp_eq] at hDodd <;>
        norm_num [hp_eq] at hp <;> norm_num <;> omega
    · interval_cases D <;> norm_num [hp_eq] at hDodd <;>
        norm_num [hp_eq] at hp <;> norm_num <;> omega
  rcases hcases with h19 | h21 | h27 | h31 | h37 | h45 | h49 | h51 | h55 | h57 | h69
  · have h := hDsupport 19 (by norm_num) (by simpa [h19])
    norm_num at h
    omega
  · have h := hDsupport 7 (by norm_num) (by simpa [h21])
    norm_num at h
    omega
  · exact Or.inl h27
  · exact Or.inr (Or.inl h31)
  · exact Or.inr (Or.inr (Or.inl h37))
  · exact Or.inr (Or.inr (Or.inr h45))
  · have h := hDsupport 7 (by norm_num) (by simpa [h49])
    norm_num at h
    omega
  · have h := hDsupport 17 (by norm_num) (by simpa [h51])
    norm_num at h
    omega
  · have h := hDsupport 11 (by norm_num) (by simpa [h55])
    norm_num at h
    omega
  · have h := hDsupport 19 (by norm_num) (by simpa [h57])
    norm_num at h
    omega
  · have h := hDsupport 23 (by norm_num) (by simpa [h69])
    norm_num at h
    omega
