-- Prove2me | solution 1 for collatz_descent_fifteen_mod_sixteen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:32:12.318546+00:00
-- url     : https://prove2.me/submissions/664a36a1-520c-476e-b755-e839ed67f28a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_descent_of_syracuse_descent
import Theorems.Thm_syracuse_descent_fifteen_mod_sixteen

theorem solution (n : ℕ) (h : n % 16 = 15) : ∃ m : ℕ, collatzStep^[m] n < n := by
  have hodd : ¬ Even n := by rw [Nat.even_iff]; omega
  exact collatz_descent_of_syracuse_descent n hodd (syracuse_descent_fifteen_mod_sixteen n h)
