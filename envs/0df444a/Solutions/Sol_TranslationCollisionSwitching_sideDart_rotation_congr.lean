-- Prove2me | solution 1 for TranslationCollisionSwitching.sideDart_rotation_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:24.380077+00:00
-- url     : https://prove2.me/submissions/fd186175-2f71-4792-bd13-ccb5ae057f8f

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
    {rho sigma : RotationSystem d V} {k : ℕ}
    (hrho : rho = sigma) (q : DeviationIndex d k) :
    sideDart d G hG start rho q = sideDart d G hG start sigma q := by
  subst sigma
  rfl
end TranslationCollisionSwitching
