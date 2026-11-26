-- Prove2me | solution 1 for TranslationReversal.reverseSimpleClassifiedReturn_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:15.883007+00:00
-- url     : https://prove2.me/submissions/19582b81-1931-4819-8476-d5ea9fb4020d

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationReversal_reversedReturnRotation_twice

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
theorem _root_.solution
    {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) :
    reverseSimpleClassifiedReturn (d := d) G hG
        (reverseSimpleClassifiedReturn (d := d) G hG q) = q := by
  apply SimpleClassifiedReturn.ext
  · apply Subtype.ext
    exact reversedReturnRotation_twice (d := d) G hG start q.sample.1 k
      q.sourceDeviation q.finishDeviation q.endpoint_eq
  · rfl
  · rfl
end TranslationReversal
