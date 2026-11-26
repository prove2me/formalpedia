-- Prove2me | solution 1 for TranslationIntegration.uncertifiedClassifiedToCertified_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:12:27.809492+00:00
-- url     : https://prove2.me/submissions/3f84779f-daf5-4dda-af0f-2066fc6918b6

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
public import Theorems.Thm_TranslationIntegration_uncertifiedClassifiedToSimple_injective
public import Theorems.Thm_TranslationIntegration_certifiedSimpleToClassified_injective

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
      (uncertifiedClassifiedToCertified (d := d) G hG :
        UncertifiedClassifiedReturn (d := d) G hG start k L →
          CertifiedClassifiedReturn (d := d) G hG start k L) :=
  (certifiedSimpleToClassified_injective (d := d) G hG).comp <|
    (uncertifiedToCertified_injective (d := d) G hG).comp <|
      uncertifiedClassifiedToSimple_injective (d := d) G hG
end TranslationIntegration
