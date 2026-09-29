-- Prove2me | solution 2 for collatz_descent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:48:15.762528+00:00
-- url     : https://prove2.me/submissions/7a8783bb-ef90-4c8e-8ffc-e69ec9f7f190
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_collatzStepMap
import Theorems.Thm_collatz_descent_even
import Theorems.Thm_collatz_descent_one_mod_four
import Theorems.Thm_collatz_descent_three_mod_four

theorem _root_.solution (n : ℕ) (hn : 1 < n) : ∃ m : ℕ, collatzStep^[m] n < n := by
  by_cases he : Even n
  · exact ⟨1, by simpa using collatz_descent_even n (by omega) he⟩
  · rw [Nat.even_iff] at he
    have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
    rcases h4 with h | h
    · exact ⟨3, collatz_descent_one_mod_four n hn h⟩
    · exact collatz_descent_three_mod_four n h

#print axioms solution
