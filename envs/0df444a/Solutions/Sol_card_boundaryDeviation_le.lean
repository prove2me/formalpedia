-- Prove2me | solution 1 for card_boundaryDeviation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:52.136995+00:00
-- url     : https://prove2.me/submissions/2b2efd1b-3eb3-4792-9809-224d56d41ad2

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_card_offset

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
    (rho : GoodOmega d G hG start k)
    (J : Finset (ValidDeviation d G hG start rho.1 k))
    (f : ValidDeviation d G hG start rho.1 k →
      ValidDeviation d G hG start rho.1 k)
    (hf : Set.InjOn f (J : Set (ValidDeviation d G hG start rho.1 k)))
    (L : ℕ) :
    (DegreeEligibleArithmetic.boundaryBad J
      (fun q ↦ internalTime (f q).1.1) k L).card ≤ L * d := by
  classical
  let B := DegreeEligibleArithmetic.boundaryBad J
    (fun q ↦ internalTime (f q).1.1) k L
  let code : B → Fin L × Offset d := fun q ↦
    (⟨k - 1 - internalTime (f q.1).1.1, by
      have hmem : k < internalTime (f q.1).1.1 + L := by
        have hqmem : q.1 ∈ DegreeEligibleArithmetic.boundaryBad J
            (fun z ↦ internalTime (f z).1.1) k L := q.2
        exact (Finset.mem_filter.mp hqmem).2
      have hlt := internalTime_lt (f q.1).1.1
      omega⟩,
    (f q.1).1.2)
  have hcode : Function.Injective code := by
    intro q r hqr
    have hfirst := congrArg (fun z : Fin L × Offset d ↦ (z.1 : ℕ)) hqr
    have hqtime := internalTime_lt (f q.1).1.1
    have hrtime := internalTime_lt (f r.1).1.1
    have htime : internalTime (f q.1).1.1 = internalTime (f r.1).1.1 := by
      dsimp only [code] at hfirst
      omega
    have hindex : (f q.1).1.1 = (f r.1).1.1 := by
      apply Fin.ext
      simp only [internalTime] at htime
      omega
    have hoffset : (f q.1).1.2 = (f r.1).1.2 :=
      congrArg (fun z : Fin L × Offset d ↦ z.2) hqr
    have hfr : f q.1 = f r.1 := by
      apply Subtype.ext
      exact Prod.ext hindex hoffset
    apply Subtype.ext
    apply hf
    · have hqmem : q.1 ∈ DegreeEligibleArithmetic.boundaryBad J
          (fun z ↦ internalTime (f z).1.1) k L := q.2
      exact (Finset.mem_filter.mp hqmem).1
    · have hrmem : r.1 ∈ DegreeEligibleArithmetic.boundaryBad J
          (fun z ↦ internalTime (f z).1.1) k L := r.2
      exact (Finset.mem_filter.mp hrmem).1
    · exact hfr
  calc
    B.card = Fintype.card B := by simp
    _ ≤ Fintype.card (Fin L × Offset d) :=
      Fintype.card_le_of_injective code hcode
    _ = L * (d - 1) := by simp [card_offset]
    _ ≤ L * d := Nat.mul_le_mul_left L (Nat.sub_le d 1)
