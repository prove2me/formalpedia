-- Prove2me | solution 1 for collatz_descent_three_mod_four
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:18:17.014785+00:00
-- url     : https://prove2.me/submissions/079cf620-ca83-46af-b8c8-5b8fb50e8703
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_descent_three_mod_sixteen
import Theorems.Thm_collatz_descent_eleven_mod_thirtytwo
import Theorems.Thm_collatz_descent_twentythree_mod_thirtytwo
import Theorems.Thm_collatz_descent_seven_mod_thirtytwo
import Theorems.Thm_collatz_descent_twentyseven_mod_thirtytwo
import Theorems.Thm_collatz_descent_fifteen_mod_sixteen

theorem solution (n : ℕ) (h : n % 4 = 3) : ∃ m : ℕ, collatzStep^[m] n < n := by
  have hcases : n % 16 = 3 ∨ n % 32 = 11 ∨ n % 32 = 23 ∨
      n % 32 = 7 ∨ n % 32 = 27 ∨ n % 16 = 15 := by omega
  rcases hcases with h1 | h1 | h1 | h1 | h1 | h1
  · exact collatz_descent_three_mod_sixteen n h1
  · exact collatz_descent_eleven_mod_thirtytwo n h1
  · exact collatz_descent_twentythree_mod_thirtytwo n h1
  · exact collatz_descent_seven_mod_thirtytwo n h1
  · exact collatz_descent_twentyseven_mod_thirtytwo n h1
  · exact collatz_descent_fifteen_mod_sixteen n h1
