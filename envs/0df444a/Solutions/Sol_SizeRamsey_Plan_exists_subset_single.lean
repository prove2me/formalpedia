-- Prove2me | solution 1 for SizeRamsey.Plan.exists_subset_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:33.347566+00:00
-- url     : https://prove2.me/submissions/b8200ab2-dcbc-4e4c-afde-e192fd63ed47

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
theorem _root_.solution {V : Type*} (x₀ : V) (S : Finset V)
    (hS : S.card ≤ 1) : ∃ x, S ⊆ {x} := by
  rcases Nat.lt_or_ge S.card 1 with h' | h'
  · rw [Nat.lt_one_iff, Finset.card_eq_zero] at h'
    exact ⟨x₀, by simp [h']⟩
  · obtain ⟨x, hx⟩ := (Finset.card_eq_one (s := S)).mp (by omega)
    exact ⟨x, hx.le⟩
end SizeRamsey.Plan
