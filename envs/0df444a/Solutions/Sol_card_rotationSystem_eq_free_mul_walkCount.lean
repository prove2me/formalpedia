-- Prove2me | solution 1 for card_rotationSystem_eq_free_mul_walkCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:12:50.572886+00:00
-- url     : https://prove2.me/submissions/b5a6c5fd-9019-4940-ab4c-78f7d0085546

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_natCard_rotationSystem
public import Theorems.Thm_card_walkCount

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
theorem _root_.solution
    (d : ℕ) [NeZero d] (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    Nat.card (RotationSystem d V) =
      (d - 1) ^ (Fintype.card V - (k - 1)) * walkCount G start k := by
  rw [natCard_rotationSystem, card_walkCount d G hG start k hk]
  rw [← pow_add]
  congr 1
  omega
