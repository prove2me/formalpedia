-- Prove2me | solution 1 for TranslationCollisionSwitching.recover_deviationRotation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:03.310503+00:00
-- url     : https://prove2.me/submissions/e255810b-9d90-4def-8fac-64160ca187a3

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
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
open TranslationCollisionSwitching
open TranslationReversal TranslationIntegration
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationCollisionSwitching.graphAdjDecidable
attribute [local instance] TranslationCollisionSwitching.vertexDecidableEq
namespace TranslationCollisionSwitching
theorem _root_.solution (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) :
    recoverRotation (d := d) G hG start
        (deviationRotation d G hG start rho.1 q.1) q.1.1
        (currentOffset d G hG start rho.1 q.1.1) = rho.1 := by
  have hv := deviation_orbitVertex_eq_of_le (d := d) G hG start rho q
    (le_refl (internalTime q.1.1))
  unfold recoverRotation
  rw [hv]
  funext v
  by_cases h : v = orbitVertex d G hG start rho.1 (internalTime q.1.1)
  · subst v
    simp [deviationRotation, currentOffset]
  · simp [deviationRotation, setOffsetAt, h]
end TranslationCollisionSwitching
