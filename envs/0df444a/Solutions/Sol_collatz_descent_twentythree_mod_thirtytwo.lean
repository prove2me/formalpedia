-- Prove2me | solution 1 for collatz_descent_twentythree_mod_thirtytwo
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:16:23.717481+00:00
-- url     : https://prove2.me/submissions/878279c5-5be8-4414-afa1-0791dc97860e

import Mathlib
import Definitions.Def_collatzStepMap

theorem solution (n : ℕ) (h : n % 32 = 23) : ∃ m : ℕ, collatzStep^[m] n < n := by
  have hodd : ∀ x : ℕ, ¬ Even x → collatzStep x = 3 * x + 1 := fun x hx => by simp [collatzStep, hx]
  have heven : ∀ x : ℕ, Even x → collatzStep x = x / 2 := fun x hx => by simp [collatzStep, hx]
  obtain ⟨j, hj⟩ : ∃ j, n = 32 * j + 23 := ⟨n / 32, by omega⟩
  refine ⟨8, ?_⟩
  have e1 : collatzStep n = 96 * j + 70 := by rw [hodd n (by rw [Nat.even_iff]; omega)]; omega
  have e2 : collatzStep (96 * j + 70) = 48 * j + 35 := by rw [heven _ (by rw [Nat.even_iff]; omega)]; omega
  have e3 : collatzStep (48 * j + 35) = 144 * j + 106 := by rw [hodd _ (by rw [Nat.even_iff]; omega)]; omega
  have e4 : collatzStep (144 * j + 106) = 72 * j + 53 := by rw [heven _ (by rw [Nat.even_iff]; omega)]; omega
  have e5 : collatzStep (72 * j + 53) = 216 * j + 160 := by rw [hodd _ (by rw [Nat.even_iff]; omega)]; omega
  have e6 : collatzStep (216 * j + 160) = 108 * j + 80 := by rw [heven _ (by rw [Nat.even_iff]; omega)]; omega
  have e7 : collatzStep (108 * j + 80) = 54 * j + 40 := by rw [heven _ (by rw [Nat.even_iff]; omega)]; omega
  have e8 : collatzStep (54 * j + 40) = 27 * j + 20 := by rw [heven _ (by rw [Nat.even_iff]; omega)]; omega
  show collatzStep (collatzStep (collatzStep (collatzStep (collatzStep (collatzStep (collatzStep
    (collatzStep n))))))) < n
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  omega
