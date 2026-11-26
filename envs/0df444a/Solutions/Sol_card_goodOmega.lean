-- Prove2me | solution 1 for card_goodOmega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:50.965642+00:00
-- url     : https://prove2.me/submissions/2581471c-bd26-45ef-860a-95688847f722

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_card_goodOmega_succ

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
noncomputable section
variable {V : Type*} [Fintype V]
theorem _root_.solution (d : ℕ) [NeZero d] (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) :
    Nat.card (GoodOmega d G hG start k) =
      simpleWalkCount G start k *
        (d - 1) ^ (Fintype.card V - (k - 1)) := by
  have h := card_goodOmega_succ d G hG (m := k - 1) start
  rw [Nat.sub_add_cancel hk] at h
  exact h
