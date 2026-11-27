-- Prove2me | solution 1 for SizeRamsey.Plan.not_c4Transversal_of_avoid_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:36.990286+00:00
-- url     : https://prove2.me/submissions/b3ef6aff-3040-4486-bd16-edc6528d4bfa

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_square
public import Theorems.Thm_SizeRamsey_Plan_exists_subset_pair

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*} {G : SimpleGraph V}
    (x₀ : V)
    (h : ∀ x y : V, ∃ a b c d : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧
      a ≠ c ∧ b ≠ d ∧ a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x ∧ a ≠ y ∧ b ≠ y ∧ c ≠ y ∧ d ≠ y)
    (S : Finset V) (hS : S.card < 3) : ¬ c4Transversal G S := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_subset_pair x₀ S (by omega)
  obtain ⟨a, b, c, d, hab, hbc, hcd, hda, hac, hbd, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h x y
  refine not_c4Transversal_of_square hab hbc hcd hda hac hbd ⟨?_, ?_, ?_, ?_⟩ <;>
    intro hm <;> have := hxy hm <;> simp_all
end SizeRamsey.Plan
