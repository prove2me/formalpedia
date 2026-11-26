-- Prove2me | solution 1 for card_startBoundary_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:19.25842+00:00
-- url     : https://prove2.me/submissions/04e50911-f874-4251-b381-052526bf9e0c

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_card_boundaryDeviation_le

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
    (rho : GoodOmega d G hG start k) (L : ℕ) :
    (DegreeEligibleArithmetic.boundaryBad Finset.univ
      (deviationStartTime d G hG start rho) k L).card ≤ L * d := by
  change (DegreeEligibleArithmetic.boundaryBad Finset.univ
    (fun q : ValidDeviation d G hG start rho.1 k ↦ internalTime q.1.1)
    k L).card ≤ L * d
  exact card_boundaryDeviation_le d G hG start rho Finset.univ id
    (fun _ _ _ _ h ↦ h) L
