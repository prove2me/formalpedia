-- Prove2me | solution 1 for card_goodOmega_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:08.957576+00:00
-- url     : https://prove2.me/submissions/9f062f9f-f439-47f9-a840-2feecb0cf4f1

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_card_forcedRotations

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
theorem _root_.solution :
    Nat.card (GoodOmega d G hG start (m + 1)) =
      Nat.card (SimpleNonbacktrackingWalk G start (m + 1)) *
        (d - 1) ^ (Fintype.card V - m) := by
  let : Fintype (GoodOmega d G hG start (m + 1)) := Fintype.ofFinite _
  let : Fintype (SimpleNonbacktrackingWalk G start (m + 1)) := Fintype.ofFinite _
  rw [Nat.card_congr (goodOmegaEquivWalkForced d G hG start), Nat.card_sigma]
  simp_rw [card_forcedRotations d G hG start]
  simp
