-- Prove2me | solution 1 for collatz_descent_of_syracuse_descent
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:29:38.962621+00:00
-- url     : https://prove2.me/submissions/ff5f2a63-c0fc-4f99-8ea9-c0ade74e2be4

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep
import Theorems.Thm_collatz_reaches_syracuse_iterate

theorem solution (n : ℕ) (hn : ¬ Even n)
    (h : ∃ t : ℕ, syracuseStep^[t] n < n) : ∃ m : ℕ, collatzStep^[m] n < n := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate n hn t
  exact ⟨M, by rw [hM]; exact ht⟩
