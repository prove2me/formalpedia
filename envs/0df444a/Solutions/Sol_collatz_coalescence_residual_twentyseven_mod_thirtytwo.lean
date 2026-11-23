-- Prove2me | solution 1 for collatz_coalescence_residual_twentyseven_mod_thirtytwo
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:03:09.051656+00:00
-- url     : https://prove2.me/submissions/1e683221-a1ad-473a-bf54-2da5f9cb33bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_coalescence_affine_progressions
import Theorems.Thm_collatz_coalescence_residual_twentyseven_mod_thirtytwo_after_affine_sieve

theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 32 = 27)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hprefix : ∀ t : ℕ, t ≤ 128 → n ≤ collatzStep^[t] n) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  by_cases h81_10 : n % 81 = 10
  · exact collatz_coalescence_affine_progressions n (by simp [h81_10])
  by_cases h9216_1563 : n % 9216 = 1563
  · exact collatz_coalescence_affine_progressions n (by simp [h9216_1563])
  exact collatz_coalescence_residual_twentyseven_mod_thirtytwo_after_affine_sieve n hlarge hclass hmod9 hprefix
    h81_10
    h9216_1563
