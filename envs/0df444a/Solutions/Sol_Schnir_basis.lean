-- Prove2me | solution 1 for Schnir.basis
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:01:32.323058+00:00
-- url     : https://prove2.me/submissions/777583bd-f1f0-4936-8dfe-4ad0cfcab562

import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Tactic.Linarith
import Theorems.Thm_Schnir_basis_of_density

/-!
# Schnirelmann's basis theorem

A set of natural numbers containing `0` with positive Schnirelmann density is an
additive basis of finite order: there is a `k` such that every natural number is a
sum of exactly `k` elements of the set. This is the theorem the Schnirelmann density
was introduced for, and the engine behind the Schnirelmann-style results that every
odd number is a bounded sum of primes.

The order is taken as `k = ⌈1 / sigma(A)⌉`, for which `k * sigma(A) >= 1`; the claim
then follows from `Schnir.basis_of_density`.
-/

open Pointwise Classical

open Pointwise Classical in
theorem solution (A : Set ℕ) (hA0 : 0 ∈ A) (hσ : 0 < schnirelmannDensity A) :
    ∃ k : ℕ, ∀ n : ℕ, ∃ t : Multiset ℕ, t.card = k ∧ (∀ x ∈ t, x ∈ A) ∧ t.sum = n := by
  have h1 : ((1 : ℝ) / schnirelmannDensity A)
      ≤ ((Nat.ceil ((1 : ℝ) / schnirelmannDensity A) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_ceil _
  have h2 : ((1 : ℝ) / schnirelmannDensity A) * schnirelmannDensity A = 1 := by
    field_simp
  have hk : 1 ≤ ((Nat.ceil ((1 : ℝ) / schnirelmannDensity A) : ℕ) : ℝ)
      * schnirelmannDensity A := by
    nlinarith [h1, h2, (le_of_lt hσ)]
  exact ⟨Nat.ceil ((1 : ℝ) / schnirelmannDensity A), Schnir.basis_of_density A hA0 _ hk⟩
