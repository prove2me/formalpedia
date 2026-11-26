-- Prove2me | solution 1 for TranslationReversal.card_eligibleSimpleClassifiedReturn_le_two_mul_certified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:12:30.143599+00:00
-- url     : https://prove2.me/submissions/43625cee-4f75-464d-9c7d-66bf6de53e8d

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationReversal_uncertifiedToCertified_injective

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
    {start : OrientedEdge G} {k L : ℕ} :
    Nat.card (EligibleSimpleClassifiedReturn (d := d) G hG start k L) ≤
      2 * Nat.card
        (CertifiedEligibleSimpleReturn (d := d) G hG start k L) := by
  rw [Nat.card_congr (eligibleCertifiedSumEquiv (d := d) G hG), Nat.card_sum]
  have hle :
      Nat.card (UncertifiedEligibleSimpleReturn (d := d) G hG start k L) ≤
        Nat.card (CertifiedEligibleSimpleReturn (d := d) G hG start k L) :=
    Nat.card_le_card_of_injective _
      (uncertifiedToCertified_injective (d := d) G hG)
  omega
end TranslationReversal
