-- Prove2me | solution 1 for collatz_coalescence_residual_fifteen_mod_sixteen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:03:10.80407+00:00
-- url     : https://prove2.me/submissions/f689a4cc-c1e3-4dbc-8701-878e39c9aa41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_coalescence_affine_progressions
import Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_affine_sieve

theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hprefix : ∀ t : ℕ, t ≤ 128 → n ≤ collatzStep^[t] n) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  by_cases h81_10 : n % 81 = 10
  · exact collatz_coalescence_affine_progressions n (by simp [h81_10])
  by_cases h2304_1743 : n % 2304 = 1743
  · exact collatz_coalescence_affine_progressions n (by simp [h2304_1743])
  by_cases h2304_1599 : n % 2304 = 1599
  · exact collatz_coalescence_affine_progressions n (by simp [h2304_1599])
  by_cases h4608_2847 : n % 4608 = 2847
  · exact collatz_coalescence_affine_progressions n (by simp [h4608_2847])
  by_cases h4608_735 : n % 4608 = 735
  · exact collatz_coalescence_affine_progressions n (by simp [h4608_735])
  by_cases h4608_991 : n % 4608 = 991
  · exact collatz_coalescence_affine_progressions n (by simp [h4608_991])
  by_cases h4608_2527 : n % 4608 = 2527
  · exact collatz_coalescence_affine_progressions n (by simp [h4608_2527])
  by_cases h4608_3039 : n % 4608 = 3039
  · exact collatz_coalescence_affine_progressions n (by simp [h4608_3039])
  by_cases h4608_4575 : n % 4608 = 4575
  · exact collatz_coalescence_affine_progressions n (by simp [h4608_4575])
  exact collatz_coalescence_residual_fifteen_mod_sixteen_after_affine_sieve n hlarge hclass hmod9 hprefix
    h81_10
    ⟨h2304_1743, h2304_1599⟩
    ⟨h4608_2847, h4608_735, h4608_991, h4608_2527, h4608_3039, h4608_4575⟩
