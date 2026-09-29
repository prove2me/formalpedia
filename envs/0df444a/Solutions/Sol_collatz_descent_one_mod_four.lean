-- Prove2me | solution 1 for collatz_descent_one_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:54:30.876+00:00
-- url     : https://prove2.me/submissions/bb71067b-546c-4d42-a08b-813323f07c90

import Mathlib
import Definitions.Def_collatzStepMap

theorem solution (n : ℕ) (hn : 1 < n) (h : n % 4 = 1) : collatzStep^[3] n < n := by
  have hodd : ¬ Even n := by rw [Nat.even_iff]; omega
  have h1 : collatzStep n = 3 * n + 1 := by simp [collatzStep, hodd]
  have he2 : Even (3 * n + 1) := by rw [Nat.even_iff]; omega
  have h2 : collatzStep (3 * n + 1) = (3 * n + 1) / 2 := by simp [collatzStep, he2]
  have he3 : Even ((3 * n + 1) / 2) := by rw [Nat.even_iff]; omega
  have h3 : collatzStep ((3 * n + 1) / 2) = ((3 * n + 1) / 2) / 2 := by simp [collatzStep, he3]
  show collatzStep (collatzStep (collatzStep n)) < n
  rw [h1, h2, h3]
  omega
