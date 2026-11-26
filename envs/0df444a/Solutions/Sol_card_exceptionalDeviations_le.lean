-- Prove2me | solution 1 for card_exceptionalDeviations_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:29.616689+00:00
-- url     : https://prove2.me/submissions/7256cada-11a4-4d32-a33e-32d6b4ae4801

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_natCard_exceptionalDeviation_le

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
theorem _root_.solution (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    (exceptionalDeviations d G hG start rho).card ≤ 4 * d := by
  let : Finite (ExceptionalDeviation d G hG start rho) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let f : {q // q ∈ exceptionalDeviations d G hG start rho} →
      ExceptionalDeviation d G hG start rho :=
    fun q ↦ ⟨q.1,
      (mem_exceptionalDeviations_iff d G hG start rho q.1).mp q.2⟩
  have hf : Function.Injective f := by
    intro q r hqr
    apply Subtype.ext
    exact congrArg (fun z : ExceptionalDeviation d G hG start rho ↦ z.1) hqr
  calc
    (exceptionalDeviations d G hG start rho).card =
        Nat.card {q // q ∈ exceptionalDeviations d G hG start rho} := by simp
    _ ≤ Nat.card (ExceptionalDeviation d G hG start rho) :=
      Nat.card_le_card_of_injective f hf
    _ ≤ 4 * d := natCard_exceptionalDeviation_le d G hG start rho
