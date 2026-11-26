-- Prove2me | solution 1 for TranslationCollisionSwitching.high_good_plan_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:52.842156+00:00
-- url     : https://prove2.me/submissions/d9732026-0570-4037-9ee8-0dd910da09ae

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationCollisionSwitching_high_switching_card_bound
public import Theorems.Thm_TranslationCollisionSwitching_degreeCutoff_mul_k_bound

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
theorem _root_.solution (start : OrientedEdge G) (k : ℕ)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    Nat.card (GoodOmega d G hG start k) * k ^ 2 ≤
      1024 * d ^ 2 * Fintype.card V * Nat.card (RotationSystem d V) := by
  have hswitch := high_switching_card_bound (d := d) G hG start k hd hhigh hkn
  have hcut := degreeCutoff_mul_k_bound (d := d) hkn
  calc
    Nat.card (GoodOmega d G hG start k) * k ^ 2 =
        (k * Nat.card (GoodOmega d G hG start k)) * k := by ring
    _ ≤ (8 * Nat.card (RotationSystem d V) *
          degreeCutoff d (Fintype.card V) k * (d - 1)) * k :=
      Nat.mul_le_mul_right k hswitch
    _ = (8 * degreeCutoff d (Fintype.card V) k * (d - 1) * k) *
          Nat.card (RotationSystem d V) := by ring
    _ ≤ (1024 * d ^ 2 * Fintype.card V) *
          Nat.card (RotationSystem d V) :=
      Nat.mul_le_mul_right _ hcut
    _ = 1024 * d ^ 2 * Fintype.card V *
          Nat.card (RotationSystem d V) := by ring
end TranslationCollisionSwitching
