-- Prove2me | solution 1 for TranslationReversal.reverseSimpleClassifiedReturn_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:21.378353+00:00
-- url     : https://prove2.me/submissions/30914bea-9f90-4aad-8a27-f39ba77f9a5d

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationReversal_reverseSimpleClassifiedReturn_involutive

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
    {start : OrientedEdge G} {k : ℕ} :
    Function.Injective
      (reverseSimpleClassifiedReturn (d := d) G hG :
        SimpleClassifiedReturn (d := d) G hG start k →
          SimpleClassifiedReturn (d := d) G hG start k) :=
  Function.Involutive.injective
    (reverseSimpleClassifiedReturn_involutive (d := d) G hG)
end TranslationReversal
