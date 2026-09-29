-- Prove2me | solution 1 for collatz_descent_seven_mod_thirtytwo
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:32:11.38705+00:00
-- url     : https://prove2.me/submissions/46ab3dc4-1d72-43bf-9d75-18b0b269ad87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_descent_of_syracuse_descent
import Theorems.Thm_syracuse_descent_seven_mod_thirtytwo

theorem solution (n : ℕ) (h : n % 32 = 7) : ∃ m : ℕ, collatzStep^[m] n < n := by
  have hodd : ¬ Even n := by rw [Nat.even_iff]; omega
  exact collatz_descent_of_syracuse_descent n hodd (syracuse_descent_seven_mod_thirtytwo n h)
