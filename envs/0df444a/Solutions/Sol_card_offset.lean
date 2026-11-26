-- Prove2me | solution 1 for card_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:49.56678+00:00
-- url     : https://prove2.me/submissions/059053d0-2b45-42db-9b23-4fe2e4b42247

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
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
theorem _root_.solution : Fintype.card (Offset d) = d - 1 := by
  classical
  rw [Fintype.card_subtype_compl (fun a : Fin d ↦ a = 0)]
  simp
