-- Prove2me | solution 1 for TranslationReversal.reversedReturnRotation_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:39.711808+00:00
-- url     : https://prove2.me/submissions/10badb11-e615-4744-825b-1ed6e6e480d0

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationReversal_classified_reverse_exteriorReturnVertices

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
      Dart.reverse G (sideDart d G hG start rho q'.1)) :
    reversedReturnRotation (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') = rho := by
  change negateVertices (d := d)
      (negateVertices (d := d) rho
        (exteriorReturnVertices (d := d) G hG start rho k q))
      (exteriorReturnVertices (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q')) = rho
  rw [classified_reverse_exteriorReturnVertices (d := d) G hG start rho k q q'
    hend]
  exact negateVertices_twice (d := d) rho
    (exteriorReturnVertices (d := d) G hG start rho k q)
end TranslationReversal
