-- Prove2me | solution 1 for card_forcedRotations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:35.153799+00:00
-- url     : https://prove2.me/submissions/25126c5b-d4f3-4e8e-b687-5fd8dbda9169

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_card_freeOffsets

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
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
variable {m : ℕ} (start : OrientedEdge G)
theorem _root_.solution (w : SimpleNonbacktrackingWalk G start (m + 1)) :
    Nat.card (ForcedRotations d G hG start w) =
      (d - 1) ^ (Fintype.card V - m) := by
  rw [Nat.card_congr (forcedRotationsEquivFreeOffsets d G hG start w)]
  exact card_freeOffsets d G start w
