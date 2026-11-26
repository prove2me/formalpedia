-- Prove2me | solution 1 for TranslationIntegration.countedEligible_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:12:20.646256+00:00
-- url     : https://prove2.me/submissions/016ddd10-09d2-4a77-a44b-f4e0ee2e58e2

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_many_eligibleDeviations

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
      4 * Nat.card (CountedEligibleReturn (d := d) G hG start k) := by
  let : Fintype (GoodOmega d G hG start k) := Fintype.ofFinite _
  let (rho : GoodOmega d G hG start k) :
      Fintype {q : ValidDeviation d G hG start rho.1 k //
        q ∈ eligibleDeviations d G hG start rho} := Fintype.ofFinite _
  have hsum : ∑ _rho : GoodOmega d G hG start k, k ≤
      ∑ rho : GoodOmega d G hG start k,
        4 * (eligibleDeviations d G hG start rho).card := by
    exact Finset.sum_le_sum fun rho _ ↦
      many_eligibleDeviations d G hG start rho hd hhigh hkn
  change k * Nat.card (GoodOmega d G hG start k) ≤
    4 * Nat.card (Σ rho : GoodOmega d G hG start k,
      {q : ValidDeviation d G hG start rho.1 k //
        q ∈ eligibleDeviations d G hG start rho})
  rw [Nat.card_sigma]
  simpa [Nat.card_eq_fintype_card, Finset.mul_sum, Nat.mul_comm] using hsum
end TranslationIntegration
