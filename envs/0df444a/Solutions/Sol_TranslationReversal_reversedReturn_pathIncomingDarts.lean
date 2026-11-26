-- Prove2me | solution 1 for TranslationReversal.reversedReturn_pathIncomingDarts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:18.125355+00:00
-- url     : https://prove2.me/submissions/0e248ba7-ad1d-491d-a383-f964260d4c91

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
    (q : ValidDeviation d G hG start rho k) :
    pathIncomingDarts d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k =
      pathIncomingDarts d G hG start rho k := by
  classical
  apply Finset.ext
  intro e
  simp only [mem_pathIncomingDarts_iff]
  rw [reversedReturn_pathVertices (d := d) G hG start rho k q]
end TranslationReversal
