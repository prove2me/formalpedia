-- Prove2me | solution 1 for TranslationIntegration.classifiedEligible_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:13:12.325826+00:00
-- url     : https://prove2.me/submissions/bebc4013-293f-4206-b92d-5881942725d2

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationIntegration_countedEligibleToClassified_injective
public import Theorems.Thm_TranslationIntegration_countedEligible_lower

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
open TranslationIntegration
open TranslationReversal
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationIntegration.graphAdjDecidable
attribute [local instance] TranslationIntegration.vertexDecidableEq
namespace TranslationIntegration
theorem _root_.solution (start : OrientedEdge G) (k : ℕ)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k * Nat.card (GoodOmega d G hG start k) ≤
      4 * Nat.card (ClassifiedEligibleReturn (d := d) G hG start k
        (degreeCutoff d (Fintype.card V) k)) := by
  calc
    k * Nat.card (GoodOmega d G hG start k) ≤
        4 * Nat.card (CountedEligibleReturn (d := d) G hG start k) :=
      countedEligible_lower (d := d) G hG start k hd hhigh hkn
    _ ≤ 4 * Nat.card (ClassifiedEligibleReturn (d := d) G hG start k
        (degreeCutoff d (Fintype.card V) k)) :=
      Nat.mul_le_mul_left 4 <| Nat.card_le_card_of_injective _
        (countedEligibleToClassified_injective (d := d) G hG start k)
end TranslationIntegration
