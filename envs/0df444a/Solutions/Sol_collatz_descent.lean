-- Prove2me | solution 1 for collatz_descent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:56:18.906911+00:00
-- url     : https://prove2.me/submissions/67bc59ff-2c9c-4083-a1cf-0a57fbdf7f05
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_descent_even
import Theorems.Thm_collatz_descent_one_mod_four
import Theorems.Thm_collatz_descent_three_mod_four

theorem solution (n : ℕ) (hn : 1 < n) : ∃ m : ℕ, collatzStep^[m] n < n := by
  by_cases he : Even n
  · exact ⟨1, by simpa using collatz_descent_even n (by omega) he⟩
  · have hmod : n % 4 = 1 ∨ n % 4 = 3 := by
      rw [Nat.even_iff] at he
      omega
    rcases hmod with h1 | h3
    · exact ⟨3, collatz_descent_one_mod_four n hn h1⟩
    · exact collatz_descent_three_mod_four n h3
