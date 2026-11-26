-- Prove2me | solution 1 for TranslationOuter.simpleWalkCount_eq_zero_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:40.609117+00:00
-- url     : https://prove2.me/submissions/e46c3b53-db7d-4faa-a60c-20d688c7f3a5

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
open TranslationOuter
open GeneralFinalRatio
noncomputable section
universe u
namespace TranslationOuter
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (start : OrientedEdge G) (k : ℕ) (hk : Fintype.card V ≤ k) :
    simpleWalkCount G start k = 0 := by
  rw [simpleWalkCount, Finite.card_eq_zero_iff]
  refine ⟨fun w ↦ ?_⟩
  have hcard := Nat.card_le_card_of_injective w.1.vertices w.2
  have : k + 1 ≤ Fintype.card V := by simpa using hcard
  omega
end TranslationOuter
