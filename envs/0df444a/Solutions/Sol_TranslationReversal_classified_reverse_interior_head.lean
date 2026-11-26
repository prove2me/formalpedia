-- Prove2me | solution 1 for TranslationReversal.classified_reverse_interior_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:55.209226+00:00
-- url     : https://prove2.me/submissions/5aae8cad-1a84-485a-91a6-bf9f33e53209

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
open TranslationReversal
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationReversal.graphAdjDecidable
attribute [local instance] TranslationReversal.vertexDecidableEq
namespace TranslationReversal
theorem _root_.solution (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1))
    (t : ℕ) (ht0 : 0 < t)
    (htc : t < returnLength d G hG start rho k q) :
    (returnRoute (d := d) G hG start
      (reversedReturnRotation (d := d) G hG start rho k q) k
      (transportDeviation (d := d) G hG start rho k q q') t).head =
    (returnRoute (d := d) G hG start rho k q
      (returnLength d G hG start rho k q - t)).head := by
  let c := returnLength d G hG start rho k q
  rw [classified_reverse_route (d := d) G hG start rho k q q' hend t ht0
    htc.le]
  simp only [Dart.head_reverse]
  rw [show c + 1 - t = (c - t) + 1 by omega, returnRoute_succ]
  simp
  rfl
end TranslationReversal
