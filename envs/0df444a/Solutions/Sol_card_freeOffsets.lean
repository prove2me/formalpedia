-- Prove2me | solution 1 for card_freeOffsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:28.756787+00:00
-- url     : https://prove2.me/submissions/730ebf0e-9b2c-4a73-864e-9cb20aceaf95

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_natCard_offset
public import Theorems.Thm_card_internalVertices

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
    Nat.card (FreeOffsets d G start w) =
      (d - 1) ^ (Fintype.card V - m) := by
  rw [Nat.card_fun, natCard_offset]
  congr 1
  classical
  let : Fintype {v : V // IsInternal G start w.1 v} := Fintype.ofFinite _
  let : Fintype {v : V // ¬ IsInternal G start w.1 v} := Fintype.ofFinite _
  have hc : Fintype.card {v : V // IsInternal G start w.1 v} = m := by
    rw [← Nat.card_eq_fintype_card]
    exact card_internalVertices G start w
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hc]
