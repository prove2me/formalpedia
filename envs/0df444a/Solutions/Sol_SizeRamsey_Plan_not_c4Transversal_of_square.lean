-- Prove2me | solution 1 for SizeRamsey.Plan.not_c4Transversal_of_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:57.821839+00:00
-- url     : https://prove2.me/submissions/edd2afda-0149-4d0f-b338-aba26ae80acc

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Theorems.Thm_SizeRamsey_Plan_isC4Map_of_adj

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*} {G : SimpleGraph V} {S : Finset V}
    {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d)
    (havoid : a ∉ S ∧ b ∉ S ∧ c ∉ S ∧ d ∉ S) : ¬ c4Transversal G S := by
  intro hS
  obtain ⟨i, hi⟩ := hS _ (isC4Map_of_adj hab hbc hcd hda hac hbd)
  fin_cases i <;> simp_all
end SizeRamsey.Plan
