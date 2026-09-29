-- Prove2me | solution 1 for OddPerfectNumber.q2_seven_q3_thirteen_external_factor_dispatch_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T17:03:49.172169+00:00
-- url     : https://prove2.me/submissions/1fec1cff-27d1-446c-8c62-c56eee15ce71

import Mathlib

theorem solution (p q4 r : Nat)
    (hcase :
      (p = 53 ∧ q4 = 23 ∧ r = 264031) ∨
      (p = 97 ∧ q4 = 29 ∧ r = 264031))
    (hallow : r = p ∨ r = 3 ∨ r = 7 ∨ r = 13 ∨ r = q4) : False := by
  rcases hcase with h | h
  all_goals rcases h with ⟨hp, hq, hr⟩
  all_goals subst p
  all_goals subst q4
  all_goals subst r
  all_goals rcases hallow with h | h | h | h | h <;> norm_num at h
