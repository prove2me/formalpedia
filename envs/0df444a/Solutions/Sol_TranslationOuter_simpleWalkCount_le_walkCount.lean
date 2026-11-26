-- Prove2me | solution 1 for TranslationOuter.simpleWalkCount_le_walkCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:34.38959+00:00
-- url     : https://prove2.me/submissions/831c76a0-8771-424f-9393-4b0a17b3ecf6

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
    (start : OrientedEdge G) (k : ℕ) :
    simpleWalkCount G start k ≤ walkCount G start k := by
  exact Nat.card_le_card_of_injective
    (fun w : SimpleNonbacktrackingWalk G start k ↦ w.1) Subtype.val_injective
end TranslationOuter
