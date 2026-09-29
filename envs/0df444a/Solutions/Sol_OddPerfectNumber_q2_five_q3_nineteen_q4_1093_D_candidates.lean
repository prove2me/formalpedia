-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_1093_D_candidates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T06:24:37.384752+00:00
-- url     : https://prove2.me/submissions/01202e20-90fb-42ed-9b72-26810a8feab8

import Mathlib

theorem solution (D p : Nat)
    (hDlt : D < 51)
    (hDodd : Odd D)
    (hp : p.Prime)
    (hpeq : p = 2 * D - 1)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = 1093) :
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45 := by
  have hnot7 : ¬ 7 ∣ D := by
    intro h7
    have hs := hDsupport 7 (by norm_num) h7
    rcases hs with h | h | h | h <;> norm_num at h
  have hnot31 : ¬ 31 ∣ D := by
    intro h31
    have hs := hDsupport 31 (by norm_num) h31
    rcases hs with h | h | h | h <;> norm_num at h
  have hnot37 : ¬ 37 ∣ D := by
    intro h37
    have hs := hDsupport 37 (by norm_num) h37
    rcases hs with h | h | h | h <;> norm_num at h
  -- Ground each bounded case without revisiting a branch closed by a
  -- preceding normalization.
  interval_cases D <;>
    norm_num at hDodd <;>
    norm_num [hpeq] at hp <;>
    norm_num [hpeq] at hnot7 <;>
    norm_num [hpeq] at hnot31 <;>
    norm_num [hpeq] at hnot37 <;>
    norm_num
