-- Prove2me | solution 1 for collatz_descent_three_mod_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:16:22.8416+00:00
-- url     : https://prove2.me/submissions/e0c7fbeb-0d36-4092-bf60-fb15167dbb61

import Mathlib
import Definitions.Def_collatzStepMap

theorem solution (n : ℕ) (h : n % 16 = 3) : ∃ m : ℕ, collatzStep^[m] n < n := by
  have hodd : ∀ x : ℕ, ¬ Even x → collatzStep x = 3 * x + 1 := fun x hx => by simp [collatzStep, hx]
  have heven : ∀ x : ℕ, Even x → collatzStep x = x / 2 := fun x hx => by simp [collatzStep, hx]
  obtain ⟨j, hj⟩ : ∃ j, n = 16 * j + 3 := ⟨n / 16, by omega⟩
  refine ⟨6, ?_⟩
  have e1 : collatzStep n = 48 * j + 10 := by
    rw [hodd n (by rw [Nat.even_iff]; omega)]; omega
  have e2 : collatzStep (48 * j + 10) = 24 * j + 5 := by
    rw [heven _ (by rw [Nat.even_iff]; omega)]; omega
  have e3 : collatzStep (24 * j + 5) = 72 * j + 16 := by
    rw [hodd _ (by rw [Nat.even_iff]; omega)]; omega
  have e4 : collatzStep (72 * j + 16) = 36 * j + 8 := by
    rw [heven _ (by rw [Nat.even_iff]; omega)]; omega
  have e5 : collatzStep (36 * j + 8) = 18 * j + 4 := by
    rw [heven _ (by rw [Nat.even_iff]; omega)]; omega
  have e6 : collatzStep (18 * j + 4) = 9 * j + 2 := by
    rw [heven _ (by rw [Nat.even_iff]; omega)]; omega
  show collatzStep (collatzStep (collatzStep (collatzStep (collatzStep (collatzStep n))))) < n
  rw [e1, e2, e3, e4, e5, e6]
  omega
