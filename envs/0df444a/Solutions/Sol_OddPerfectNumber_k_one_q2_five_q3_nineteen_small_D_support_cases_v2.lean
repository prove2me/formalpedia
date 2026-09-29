-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_support_cases_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T10:20:06.800016+00:00
-- url     : https://prove2.me/submissions/89d8bb3e-6b3c-4520-b833-bedb51674322

import Mathlib

theorem solution (D p q4 : Nat)
    (hDlt : D < 225)
    (hDodd : Odd D)
    (hp : p.Prime)
    (hpeq : p = 2 * D - 1)
    (hq4gt : 19 < q4)
    (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) :
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45 ∨ D = 57 ∨ D = 75 ∨ D = 135 := by
  have hnot7 : ¬ 7 ∣ D := by
    intro h7
    have hs := hDsupport 7 (by norm_num) h7
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot11 : ¬ 11 ∣ D := by
    intro h11
    have hs := hDsupport 11 (by norm_num) h11
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot13 : ¬ 13 ∣ D := by
    intro h13
    have hs := hDsupport 13 (by norm_num) h13
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot17 : ¬ 17 ∣ D := by
    intro h17
    have hs := hDsupport 17 (by norm_num) h17
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot23 : ¬ 23 ∣ D := by
    intro h23
    have hs := hDsupport 23 (by norm_num) h23
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot29 : ¬ 29 ∣ D := by
    intro h29
    have hs := hDsupport 29 (by norm_num) h29
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot31 : ¬ 31 ∣ D := by
    intro h31
    have hs := hDsupport 31 (by norm_num) h31
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot37 : ¬ 37 ∣ D := by
    intro h37
    have hs := hDsupport 37 (by norm_num) h37
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot41 : ¬ 41 ∣ D := by
    intro h41
    have hs := hDsupport 41 (by norm_num) h41
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot43 : ¬ 43 ∣ D := by
    intro h43
    have hs := hDsupport 43 (by norm_num) h43
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot47 : ¬ 47 ∣ D := by
    intro h47
    have hs := hDsupport 47 (by norm_num) h47
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot53 : ¬ 53 ∣ D := by
    intro h53
    have hs := hDsupport 53 (by norm_num) h53
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot59 : ¬ 59 ∣ D := by
    intro h59
    have hs := hDsupport 59 (by norm_num) h59
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot67 : ¬ 67 ∣ D := by
    intro h67
    have hs := hDsupport 67 (by norm_num) h67
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot79 : ¬ 79 ∣ D := by
    intro h79
    have hs := hDsupport 79 (by norm_num) h79
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot97 : ¬ 97 ∣ D := by
    intro h97
    have hs := hDsupport 97 (by norm_num) h97
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot139 : ¬ 139 ∣ D := by
    intro h139
    have hs := hDsupport 139 (by norm_num) h139
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot157 : ¬ 157 ∣ D := by
    intro h157
    have hs := hDsupport 157 (by norm_num) h157
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot199 : ¬ 199 ∣ D := by
    intro h199
    have hs := hDsupport 199 (by norm_num) h199
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega
  have hnot211 : ¬ 211 ∣ D := by
    intro h211
    have hs := hDsupport 211 (by norm_num) h211
    rcases hs with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · omega

  interval_cases D <;>
    norm_num at hDodd <;>
    norm_num [hpeq] at hp <;>
    norm_num [hpeq] at hnot7 <;>
    norm_num [hpeq] at hnot11 <;>
    norm_num [hpeq] at hnot13 <;>
    norm_num [hpeq] at hnot17 <;>
    norm_num [hpeq] at hnot23 <;>
    norm_num [hpeq] at hnot29 <;>
    norm_num [hpeq] at hnot31 <;>
    norm_num [hpeq] at hnot37 <;>
    norm_num [hpeq] at hnot41 <;>
    norm_num [hpeq] at hnot43 <;>
    norm_num [hpeq] at hnot47 <;>
    norm_num [hpeq] at hnot53 <;>
    norm_num [hpeq] at hnot59 <;>
    norm_num [hpeq] at hnot67 <;>
    norm_num [hpeq] at hnot79 <;>
    norm_num [hpeq] at hnot97 <;>
    norm_num [hpeq] at hnot139 <;>
    norm_num [hpeq] at hnot157 <;>
    norm_num [hpeq] at hnot199 <;>
    norm_num [hpeq] at hnot211 <;>
    norm_num
