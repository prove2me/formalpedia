-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T07:22:15.930269+00:00
-- url     : https://prove2.me/submissions/734a0d61-cba5-445d-937b-2a435a85cc94

import Mathlib

theorem solution (D p q4 : Nat) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hq4div : q4 ∣ D) :
    (D = 31 ∧ q4 = 31) ∨ (D = 37 ∧ q4 = 37) ∨
      (D = 79 ∧ q4 = 79) ∨ (D = 87 ∧ q4 = 29) ∨
      (D = 97 ∧ q4 = 97) := by
  rcases hq4div with ⟨k, hk⟩
  have hq4lo : 24 ≤ q4 := by omega
  have hkbound : k ≤ 4 := by
    nlinarith [hDlt, hk, hq4lo]
  interval_cases k
  · norm_num [hk] at hDodd
  · have hq4le : q4 ≤ 110 := by omega
    by_cases hq4small : q4 ≤ 47
    · have hq4low : 24 ≤ q4 := hq4lo
      interval_cases q4 <;> (try norm_num at hq4prime) <;> (try norm_num at hk) <;> (try norm_num [hk, hp_eq] at hp) <;> norm_num [hk]
    · by_cases hq4mid : q4 ≤ 71
      · have hq4low : 48 ≤ q4 := by omega
        interval_cases q4 <;> (try norm_num at hq4prime) <;> (try norm_num at hk) <;> (try norm_num [hk, hp_eq] at hp) <;> norm_num [hk]
      · by_cases hq4high : q4 ≤ 95
        · have hq4low : 72 ≤ q4 := by omega
          interval_cases q4 <;> (try norm_num at hq4prime) <;> (try norm_num at hk) <;> (try norm_num [hk, hp_eq] at hp) <;> norm_num [hk]
        · have hq4low : 96 ≤ q4 := by omega
          interval_cases q4 <;> (try norm_num at hq4prime) <;> (try norm_num at hk) <;> (try norm_num [hk, hp_eq] at hp) <;> norm_num [hk]
  · rcases hDodd with ⟨t, ht⟩
    omega
  · have hq4le : q4 ≤ 36 := by omega
    have hq4low : 24 ≤ q4 := hq4lo
    interval_cases q4 <;> (try norm_num at hq4prime) <;> (try norm_num at hk) <;> (try norm_num [hk, hp_eq] at hp) <;> norm_num [hk]
  · rcases hDodd with ⟨t, ht⟩
    omega
