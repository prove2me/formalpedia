-- Prove2me | solution 1 for TranslationIntegration.classified_le_two_mul_certified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:13:15.030786+00:00
-- url     : https://prove2.me/submissions/b27f42b2-107c-425b-9e59-5d63452a1395

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationIntegration_uncertifiedClassifiedToCertified_injective

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
theorem _root_.solution
    (start : OrientedEdge G) (k L : ℕ) :
    Nat.card (ClassifiedEligibleReturn (d := d) G hG start k L) ≤
      2 * Nat.card (CertifiedClassifiedReturn (d := d) G hG start k L) := by
  let E := ClassifiedEligibleReturn (d := d) G hG start k L
  let p : E → Prop := ClassifiedReturnCertified (d := d) G hG
  let : DecidablePred p := Classical.decPred _
  change Nat.card E ≤ 2 * Nat.card {q : E // p q}
  have hUC : Nat.card {q : E // ¬ p q} ≤ Nat.card {q : E // p q} :=
    Nat.card_le_card_of_injective _ <|
      uncertifiedClassifiedToCertified_injective (d := d) G hG
  have hpartition : Nat.card E =
      Nat.card {q : E // p q} + Nat.card {q : E // ¬ p q} := by
    rw [Nat.card_congr (subtypeOrNotEquiv p), Nat.card_sum]
  omega
end TranslationIntegration
