-- Prove2me | solution 1 for SizeRamsey.Plan.exists_subset_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:29.515906+00:00
-- url     : https://prove2.me/submissions/1885bb2f-674f-4c84-b8bd-694e23f83325

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*} [DecidableEq V] (x₀ : V) (S : Finset V)
    (hS : S.card ≤ 2) : ∃ x y, S ⊆ {x, y} := by
  rcases Nat.lt_or_ge S.card 2 with h | h
  · rcases Nat.lt_or_ge S.card 1 with h' | h'
    · rw [Nat.lt_one_iff, Finset.card_eq_zero] at h'
      exact ⟨x₀, x₀, by simp [h']⟩
    · obtain ⟨x, hx⟩ := (Finset.card_eq_one (s := S)).mp (by omega)
      exact ⟨x, x, by rw [hx]; simp⟩
  · obtain ⟨x, y, -, hxy⟩ := (Finset.card_eq_two (s := S)).mp (by omega)
    exact ⟨x, y, hxy.le⟩
end SizeRamsey.Plan
