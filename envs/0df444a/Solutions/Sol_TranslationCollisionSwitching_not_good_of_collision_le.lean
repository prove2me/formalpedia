-- Prove2me | solution 1 for TranslationCollisionSwitching.not_good_of_collision_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:52.003812+00:00
-- url     : https://prove2.me/submissions/6f4caa90-a18c-49b6-ba2c-7d038a913b81

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
    (rho : RotationSystem d V) (k t : ℕ) (htk : t ≤ k)
    (hcollision : HasCollisionAt (d := d) G hG start rho t) :
    ¬ IsGood d G hG start rho k := by
  intro hgood
  obtain ⟨s, hvertices⟩ := hcollision
  have hfin :
      (⟨(s : ℕ), by omega⟩ : Fin (k + 1)) = ⟨t, by omega⟩ :=
    hgood hvertices
  have hst : (s : ℕ) = t := congrArg Fin.val hfin
  omega
end TranslationCollisionSwitching
