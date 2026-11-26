-- Prove2me | solution 1 for TranslationReversal.certified_or_reverse_certified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:28.861922+00:00
-- url     : https://prove2.me/submissions/a8222873-3c04-441b-8f14-6d67afdf3c44

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
open TranslationReversal
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationReversal.graphAdjDecidable
attribute [local instance] TranslationReversal.vertexDecidableEq
namespace TranslationReversal
theorem _root_.solution
    {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) :
    SimpleReturnCertified (d := d) G hG q ∨
      SimpleReturnCertified (d := d) G hG
        (reverseSimpleClassifiedReturn (d := d) G hG q) := by
  exact le_total (q.finish.1 : ℕ) (q.source.1 : ℕ)
end TranslationReversal
