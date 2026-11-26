-- Prove2me | solution 1 for TranslationCollisionSwitching.high_switching_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:02.369553+00:00
-- url     : https://prove2.me/submissions/ae45411b-0c1c-4f7e-bc6a-9c46f73e0704

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationIntegration_certified_lower
public import Theorems.Thm_TranslationCollisionSwitching_card_certified_le_target_mul

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
    k * Nat.card (GoodOmega d G hG start k) ≤
      8 * Nat.card (RotationSystem d V) *
        degreeCutoff d (Fintype.card V) k * (d - 1) := by
  calc
    k * Nat.card (GoodOmega d G hG start k) ≤
        8 * Nat.card (CertifiedClassifiedReturn (d := d) G hG start k
          (degreeCutoff d (Fintype.card V) k)) :=
      certified_lower (d := d) G hG start k hd hhigh hkn
    _ ≤ 8 * (Nat.card (RotationSystem d V) *
          degreeCutoff d (Fintype.card V) k * (d - 1)) :=
      Nat.mul_le_mul_left 8 <|
        card_certified_le_target_mul (d := d) G hG
    _ = 8 * Nat.card (RotationSystem d V) *
          degreeCutoff d (Fintype.card V) k * (d - 1) := by ring
end TranslationCollisionSwitching
