-- Prove2me | solution 1 for SizeRamsey.Plan.not_c4Transversal_of_avoid_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:34.322737+00:00
-- url     : https://prove2.me/submissions/03e753d0-435f-4070-821b-a54e249f0310

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_square
public import Theorems.Thm_SizeRamsey_Plan_exists_subset_single

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*} {G : SimpleGraph V}
    (x₀ : V)
    (h : ∀ x : V, ∃ a b c d : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧
      a ≠ c ∧ b ≠ d ∧ a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x)
    (S : Finset V) (hS : S.card < 2) : ¬ c4Transversal G S := by
  obtain ⟨x, hx⟩ := exists_subset_single x₀ S (by omega)
  obtain ⟨a, b, c, d, hab, hbc, hcd, hda, hac, hbd, h1, h2, h3, h4⟩ := h x
  refine not_c4Transversal_of_square hab hbc hcd hda hac hbd ⟨?_, ?_, ?_, ?_⟩ <;>
    intro hm <;> have := hx hm <;> simp_all
end SizeRamsey.Plan
