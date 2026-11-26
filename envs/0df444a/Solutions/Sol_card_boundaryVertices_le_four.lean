-- Prove2me | solution 1 for card_boundaryVertices_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:07.558005+00:00
-- url     : https://prove2.me/submissions/f0c5acc9-f945-4a67-aa7b-7b1583e6fade

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
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
theorem _root_.solution (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ) :
    (boundaryVertices d G hG start rho k).card ≤ 4 := by
  exact Finset.card_insert_le _ _ |>.trans <| by
    have h₁ := Finset.card_insert_le
      (orbitVertex d G hG start rho 1)
      ({orbitVertex d G hG start rho (k-1), orbitVertex d G hG start rho k} : Finset V)
    have h₂ := Finset.card_insert_le
      (orbitVertex d G hG start rho (k-1))
      ({orbitVertex d G hG start rho k} : Finset V)
    simp only [Finset.card_singleton] at h₂
    omega
