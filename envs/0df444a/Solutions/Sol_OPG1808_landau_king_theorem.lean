-- Prove2me | solution 1 for OPG1808.landau_king_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:49:08.155272+00:00
-- url     : https://prove2.me/submissions/65dd0086-65d5-4937-9601-7b00abc23bde

import Mathlib

set_option autoImplicit false

/-! The target's preamble defines `OPG1808.IsTournament` inline (no Definitions bundle). A proof
may not import its own target module, and redeclaring the same name would clash with it, so the
statement below is written against a local alias with an IDENTICAL body under a distinct
namespace. It is definitionally equal to the target's constant, so `solution` has the target's
type up to delta-unfolding. -/
namespace OPG1808Sol

abbrev IsTournament {V : Type} (D : Digraph V) : Prop :=
  (∀ v : V, ¬ D.Adj v v) ∧
    ∀ a b : V, a ≠ b → (D.Adj a b ∨ D.Adj b a) ∧ ¬ (D.Adj a b ∧ D.Adj b a)

end OPG1808Sol

open OPG1808Sol in
theorem solution
    {V : Type} [Fintype V] [Nonempty V]
    (D : Digraph V)
    (ht : IsTournament D) :
    ∃ v : V, ∀ u : V, u = v ∨ D.Adj v u ∨ ∃ w : V, D.Adj v w ∧ D.Adj w u := by
  classical
  obtain ⟨hloop, htour⟩ := ht
  -- a vertex of maximum out-degree is a king
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image Finset.univ
    (fun x : V => (Finset.univ.filter (fun w => D.Adj x w)).card) Finset.univ_nonempty
  refine ⟨v, fun u => ?_⟩
  by_contra hcon
  have huv : u ≠ v := fun h => hcon (Or.inl h)
  have hvu : ¬ D.Adj v u := fun h => hcon (Or.inr (Or.inl h))
  have hw : ∀ w : V, D.Adj v w → ¬ D.Adj w u :=
    fun w hvw hwu => hcon (Or.inr (Or.inr ⟨w, hvw, hwu⟩))
  have huv' : D.Adj u v := by
    rcases (htour u v huv).1 with h | h
    · exact h
    · exact absurd h hvu
  -- `u` beats `v` and everything `v` beats, so its out-degree is strictly larger
  have hsub : insert v (Finset.univ.filter (fun w => D.Adj v w)) ⊆
      Finset.univ.filter (fun w => D.Adj u w) := by
    intro w hw'
    rw [Finset.mem_insert] at hw'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ w, ?_⟩
    rcases hw' with rfl | hw'
    · exact huv'
    · rw [Finset.mem_filter] at hw'
      have hwu : w ≠ u := by
        rintro rfl
        exact hvu hw'.2
      rcases (htour w u hwu).1 with h | h
      · exact absurd h (hw w hw'.2)
      · exact h
  have hvnot : v ∉ Finset.univ.filter (fun w => D.Adj v w) := by
    rw [Finset.mem_filter]
    exact fun h => hloop v h.2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hvnot] at hcard
  have hmax := hv u (Finset.mem_univ u)
  omega

#print axioms solution
