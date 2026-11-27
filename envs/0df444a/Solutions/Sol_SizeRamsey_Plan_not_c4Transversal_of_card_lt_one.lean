-- Prove2me | solution 1 for SizeRamsey.Plan.not_c4Transversal_of_card_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:40.760694+00:00
-- url     : https://prove2.me/submissions/4fb70771-5b37-4121-8432-299877092b7a

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_square

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) (S : Finset V) (hS : S.card < 1) : ¬ c4Transversal G S := by
  rw [Nat.lt_one_iff, Finset.card_eq_zero] at hS
  subst hS
  exact not_c4Transversal_of_square hab hbc hcd hda hac hbd (by simp)
end SizeRamsey.Plan
