-- Prove2me | solution 1 for collatz_descent_even
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:54:30.077372+00:00
-- url     : https://prove2.me/submissions/2b65e288-efd1-4314-a038-c72bb759229f

import Mathlib
import Definitions.Def_collatzStepMap

theorem solution (n : ℕ) (hn : 0 < n) (he : Even n) : collatzStep n < n := by
  have h : collatzStep n = n / 2 := by simp [collatzStep, he]
  rw [h]
  omega
