-- Prove2me | solution 1 for collatz_iterate_pos
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:54:30.486711+00:00
-- url     : https://prove2.me/submissions/cd37a06d-7863-43f9-806b-5f869186d886

import Mathlib
import Definitions.Def_collatzStepMap

theorem solution (m n : ℕ) (hn : 0 < n) : 0 < collatzStep^[m] n := by
  induction m generalizing n with
  | zero => simpa using hn
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      refine ih _ ?_
      by_cases h : Even n
      · have hstep : collatzStep n = n / 2 := by simp [collatzStep, h]
        obtain ⟨t, ht⟩ := h
        rw [hstep]
        omega
      · have hstep : collatzStep n = 3 * n + 1 := by simp [collatzStep, h]
        rw [hstep]
        omega
