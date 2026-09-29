-- Prove2me | solution 1 for OddPerfectNumber.q2_seven_q3_eleven_external_factor_dispatch_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T16:59:50.642817+00:00
-- url     : https://prove2.me/submissions/283e9074-9c2f-4981-92aa-e9c4308c2156

import Mathlib

theorem solution (p q4 r : Nat)
    (hcase :
      (p = 173 ∧ q4 = 29 ∧ r = 13933) ∨
      (p = 197 ∧ q4 = 29 ∧ r = 88009573) ∨
      (p = 73 ∧ q4 = 37 ∧ r = 127) ∨
      (p = 53 ∧ q4 = 47 ∧ r = 2237))
    (hallow : r = p ∨ r = 3 ∨ r = 7 ∨ r = 11 ∨ r = q4) : False := by
  rcases hcase with h | h | h | h
  all_goals rcases h with ⟨hp, hq, hr⟩
  all_goals subst p
  all_goals subst q4
  all_goals subst r
  all_goals rcases hallow with h | h | h | h | h <;> norm_num at h
