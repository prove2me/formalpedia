-- Prove2me | solution 1 for TranslationCollisionSwitching.firstCollisionTime_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:31.220884+00:00
-- url     : https://prove2.me/submissions/fcecf629-ee73-4561-b3ab-5f9e03b51d0b

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
theorem _root_.solution (start : OrientedEdge G) (rho : RotationSystem d V) :
    0 < firstCollisionTime (d := d) G hG start rho := by
  obtain ⟨s, -⟩ := firstCollision_spec (d := d) G hG start rho
  exact Nat.zero_lt_of_lt s.isLt
end TranslationCollisionSwitching
