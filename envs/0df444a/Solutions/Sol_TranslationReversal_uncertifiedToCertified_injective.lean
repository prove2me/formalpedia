-- Prove2me | solution 1 for TranslationReversal.uncertifiedToCertified_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:47.735317+00:00
-- url     : https://prove2.me/submissions/d67dc69b-ca47-422e-a56f-0311717eb00a

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationReversal_reverseSimpleClassifiedReturn_injective

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
    Function.Injective
      (uncertifiedToCertified (d := d) G hG :
        UncertifiedEligibleSimpleReturn (d := d) G hG start k L →
          CertifiedEligibleSimpleReturn (d := d) G hG start k L) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply reverseSimpleClassifiedReturn_injective (d := d) G hG
  exact congrArg (fun z ↦ z.1.1) hab
end TranslationReversal
