-- Prove2me | solution 1 for Schnir.basis_of_density
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T08:32:07.806359+00:00
-- url     : https://prove2.me/submissions/d420061f-fcfe-41ff-b119-46718fc6b0e3

import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Tactic.Linarith
import Theorems.Thm_Schnir_mann_iterate

/-!
# From density one to an exact-order basis

If `k * sigma(A) >= 1` and `0 in A`, then every natural number is a sum of exactly
`k` elements of `A` (with multiplicity). Follows from `Schnir.mann_iterate` together
with the fact that a set of Schnirelmann density `1` contains every positive natural.
-/

open Pointwise Classical

open Pointwise Classical in
theorem solution (A : Set ℕ) (hA0 : 0 ∈ A) (k : ℕ)
    (hk : 1 ≤ (k : ℝ) * schnirelmannDensity A) :
    ∀ n : ℕ, ∃ t : Multiset ℕ, t.card = k ∧ (∀ x ∈ t, x ∈ A) ∧ t.sum = n := by
  have hiter := Schnir.mann_iterate A hA0 k
  rw [min_eq_left hk] at hiter
  have h2 : {0}ᶜ ⊆ {n | ∃ t : Multiset ℕ, t.card = k ∧ (∀ x ∈ t, x ∈ A) ∧ t.sum = n} :=
    schnirelmannDensity_eq_one_iff.1 (le_antisymm schnirelmannDensity_le_one hiter)
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Multiset.replicate k 0, Multiset.card_replicate k 0, fun x hx => by
      rw [(Multiset.mem_replicate.1 hx).2]; exact hA0, by
      rw [Multiset.sum_replicate]; simp⟩
  · exact h2 (by show n ≠ 0; omega)
