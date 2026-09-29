-- Prove2me | solution 1 for OddPerfectNumber.prime_mod15_filter_gt17_lt500_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T14:06:44.103795+00:00
-- url     : https://prove2.me/submissions/168584fd-40e4-4566-922d-f82117fa1d9a

import Mathlib

theorem solution (q4 : Nat)
    (hprime : q4.Prime) (hlo : 17 < q4) (hmod : q4 % 15 = 1) (hhi : q4 < 500) :
    q4 = 31 ∨ q4 = 61 ∨ q4 = 151 ∨ q4 = 181 ∨ q4 = 211 ∨ q4 = 241 ∨ q4 = 271 ∨ q4 = 331 ∨ q4 = 421 := by
  obtain ⟨k, hk⟩ : ∃ k, q4 = 15 * k + 1 := ⟨q4 / 15, by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hk33 : k ≤ 33 := by omega
  by_cases hk17 : k ≤ 17
  · interval_cases k <;> norm_num at hk <;> subst hk <;> norm_num at hprime <;> norm_num
  · have hk18 : 18 ≤ k := by omega
    interval_cases k <;> norm_num at hk <;> subst hk <;> norm_num at hprime <;> norm_num
