-- Prove2me | solution 1 for collatz_coalescence_residual_seven_mod_thirtytwo
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:03:10.831199+00:00
-- url     : https://prove2.me/submissions/2144fea6-5258-4d40-bad9-9711d961e224
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_coalescence_affine_progressions
import Theorems.Thm_collatz_coalescence_residual_seven_mod_thirtytwo_after_affine_sieve

theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 32 = 7)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hprefix : ∀ t : ℕ, t ≤ 128 → n ≤ collatzStep^[t] n) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  by_cases h81_10 : n % 81 = 10
  · exact collatz_coalescence_affine_progressions n (by simp [h81_10])
  by_cases h4608_4071 : n % 4608 = 4071
  · exact collatz_coalescence_affine_progressions n (by simp [h4608_4071])
  by_cases h9216_7783 : n % 9216 = 7783
  · exact collatz_coalescence_affine_progressions n (by simp [h9216_7783])
  exact collatz_coalescence_residual_seven_mod_thirtytwo_after_affine_sieve n hlarge hclass hmod9 hprefix
    h81_10
    h4608_4071
    h9216_7783
