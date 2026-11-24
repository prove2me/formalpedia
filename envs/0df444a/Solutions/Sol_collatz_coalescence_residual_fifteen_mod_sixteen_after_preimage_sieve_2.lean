-- Prove2me | solution 2 for collatz_coalescence_residual_fifteen_mod_sixteen_after_preimage_sieve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T07:22:24.555354+00:00
-- url     : https://prove2.me/submissions/8ad19c72-30c3-4d1f-9304-dc35f9d1898f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_smaller_predecessor_eighteen_steps_mod_2187
import Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_eighteen_step_classes

theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  by_cases hr : n % 2187 ∈ [205, 325, 919, 991, 1000, 1090, 1171, 2170]
  · obtain ⟨k, hk, hkn, hreach⟩ := collatz_smaller_predecessor_eighteen_steps_mod_2187 n hr
    exact ⟨k, 0, 18, hk, hkn, hreach.symm⟩
  · exact collatz_coalescence_residual_fifteen_mod_sixteen_after_eighteen_step_classes
      n hlarge hclass hmod9 hpreimage h81 h2304 h4608 hr
