-- Prove2me | solution 1 for TranslationIntegration.uncertifiedClassifiedToSimple_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:21.124709+00:00
-- url     : https://prove2.me/submissions/3c2de41b-043c-407d-9515-049f2a04d333

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
    {start : OrientedEdge G} {k L : ℕ} :
    Function.Injective
      (uncertifiedClassifiedToSimple (d := d) G hG :
        UncertifiedClassifiedReturn (d := d) G hG start k L →
          UncertifiedEligibleSimpleReturn (d := d) G hG start k L) := by
  intro q r hqr
  apply Subtype.ext
  apply ClassifiedEligibleReturn.ext
  · exact congrArg (fun z ↦ z.1.1.sample) hqr
  · exact congrArg (fun z ↦ z.1.1.source) hqr
  · exact congrArg (fun z ↦ z.1.1.finish) hqr
end TranslationIntegration
