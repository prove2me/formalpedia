-- Prove2me | solution 1 for OddPerfectNumber.prime_mod15_filter_gt31_le170_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T16:48:48.752219+00:00
-- url     : https://prove2.me/submissions/fd090389-0dff-4c1a-afe5-96d73ab1bdc2

import Mathlib

theorem solution (q4 : Nat)
    (hprime : q4.Prime) (hlo : 31 < q4) (hmod : q4 % 15 = 1) (hhi : q4 ≤ 170) :
    q4 = 61 ∨ q4 = 151 := by
  obtain ⟨k, hk⟩ : ∃ k, q4 = 15 * k + 1 := ⟨q4 / 15, by omega⟩
  have hk3 : 3 ≤ k := by omega
  have hk11 : k ≤ 11 := by omega
  interval_cases k <;> norm_num at hk <;> subst hk <;> norm_num at hprime <;> norm_num
