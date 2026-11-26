-- Prove2me | solution 1 for TranslationReversal.reversedReturn_returnBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:27.31457+00:00
-- url     : https://prove2.me/submissions/0b1c50df-38da-467c-9325-c43a8ca4bef8

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
theorem _root_.solution (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k)
    (a : DeviationIndex d k) :
    returnBase d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) a =
      returnBase d G hG start rho a := by
  apply (Dart.phi d G hG
    (reversedReturnRotation (d := d) G hG start rho k q)).injective
  rw [phi_returnBase, reversedReturn_sideDart (d := d) G hG start rho k q a]
  symm
  calc
    Dart.phi d G hG
        (reversedReturnRotation (d := d) G hG start rho k q)
        (returnBase d G hG start rho a) =
      Dart.phi d G hG rho (returnBase d G hG start rho a) := by
        apply phi_eq_of_eq_at_head (d := d) G hG
        apply reversedReturnRotation_eq_on_path (d := d) G hG start rho k q
        rw [returnBase_head]
        exact mem_pathVertices d G hG start rho k
          ⟨internalTime a.1,
            lt_trans (internalTime_lt a.1) (Nat.lt_succ_self k)⟩
    _ = sideDart d G hG start rho a :=
      phi_returnBase d G hG start rho a
end TranslationReversal
