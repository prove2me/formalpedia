-- Prove2me | solution 1 for collatz_coalescence_residual_fifteen_mod_sixteen_after_eighteen_step_classes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:53:46.790064+00:00
-- url     : https://prove2.me/submissions/5af6fc29-411e-4e67-af12-4d05c7d75afb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_smaller_predecessor_twentythree_steps_mod_19683
import Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_twentythree_step_classes

theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575)
    (h2187 : n % 2187 ∉ [205, 325, 919, 991, 1000, 1090, 1171, 2170]) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  by_cases h19683 : n % 19683 ∈ ([154, 433, 1384, 1663, 2134, 2548, 3268, 3364,
      3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517,
      6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187,
      12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376] : List ℕ)
  · obtain ⟨k, hk, hkn, hstep⟩ := collatz_smaller_predecessor_twentythree_steps_mod_19683 n h19683
    exact ⟨k, 0, 23, hk, hkn, hstep.symm⟩
  · exact collatz_coalescence_residual_fifteen_mod_sixteen_after_twentythree_step_classes
      n hlarge hclass hmod9 hpreimage h81 h2304 h4608 h2187 h19683
