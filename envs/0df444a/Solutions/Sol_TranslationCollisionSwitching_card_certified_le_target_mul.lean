-- Prove2me | solution 1 for TranslationCollisionSwitching.card_certified_le_target_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:52.886184+00:00
-- url     : https://prove2.me/submissions/5f38a16b-8359-4be4-805e-5df0cd894ef7

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_natCard_offset
public import Theorems.Thm_TranslationCollisionSwitching_certifiedCode_injective

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
theorem _root_.solution {start : OrientedEdge G} {k L : ℕ} :
    Nat.card (CertifiedClassifiedReturn (d := d) G hG start k L) ≤
      Nat.card (RotationSystem d V) * L * (d - 1) := by
  calc
    Nat.card (CertifiedClassifiedReturn (d := d) G hG start k L) ≤
        Nat.card (RotationSystem d V × (Fin L × Offset d)) :=
      Nat.card_le_card_of_injective _ (certifiedCode_injective (d := d) G hG)
    _ = Nat.card (RotationSystem d V) * L * (d - 1) := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_fin, natCard_offset]
      ring
end TranslationCollisionSwitching
