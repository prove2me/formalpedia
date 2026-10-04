-- Prove2me | solution 2 for Schnir.basis
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:25:16.327398+00:00
-- url     : https://prove2.me/submissions/a3b34443-34f0-422d-940c-9dec8638d4ba

import Theorems.Thm_Schnir_basis_of_density

/-!
Closes `Schnir.basis` — **Schnirelmann's theorem** (1930): a set of natural numbers
containing `0` with positive Schnirelmann density is an additive basis of finite order.

The finisher applies the proved `Schnir.basis_of_density` at `k := ⌊1/σ(A)⌋₊ + 1`, which
satisfies `1 ≤ k * σ(A)` since `σ(A) > 0`.
-/

open Pointwise Classical

theorem solution (A : Set ℕ) (hA0 : 0 ∈ A) (hσ : 0 < schnirelmannDensity A) :
    ∃ k : ℕ, ∀ n : ℕ, ∃ t : Multiset ℕ, t.card = k ∧ (∀ x ∈ t, x ∈ A) ∧ t.sum = n := by
  refine ⟨Nat.floor (1 / schnirelmannDensity A) + 1, fun n => ?_⟩
  have hlt : (1 : ℝ) / schnirelmannDensity A
      < (Nat.floor (1 / schnirelmannDensity A) + 1 : ℕ) :=
    by exact_mod_cast Nat.lt_floor_add_one _
  have hkey : (1 : ℝ) ≤ ((Nat.floor (1 / schnirelmannDensity A) + 1 : ℕ) : ℝ)
      * schnirelmannDensity A := by
    rw [div_lt_iff₀ hσ] at hlt
    linarith
  exact Schnir.basis_of_density A hA0 _ hkey n
