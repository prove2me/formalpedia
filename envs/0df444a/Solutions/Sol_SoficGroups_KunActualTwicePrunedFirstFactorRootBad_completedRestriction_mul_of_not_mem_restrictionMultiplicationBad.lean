-- Prove2me | solution 1 for SoficGroups.KunActualTwicePrunedFirstFactorRootBad.completedRestriction_mul_of_not_mem_restrictionMultiplicationBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/d8506950-f5a4-4812-8e46-259aaafe8649

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualTwicePrunedFirstFactorRootBad
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualTwicePrunedFirstFactorRootBad
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p q r : Equiv.Perm V) (Z : Finset V)
    (x : {v : V // v ∈ Z})
    (hx : (x : V) ∉ restrictionMultiplicationBad p q r Z) :
    completedRestriction r Z x =
      (completedRestriction p Z * completedRestriction q Z) x := by
  classical
  have hgood : ¬ (q (x : V) ∉ Z ∨ r (x : V) ∉ Z ∨
      r (x : V) ≠ p (q (x : V))) := by
    intro h
    exact hx (Finset.mem_filter.mpr ⟨x.property, h⟩)
  have hq : q (x : V) ∈ Z := by
    by_contra hn
    exact hgood (Or.inl hn)
  have hr : r (x : V) ∈ Z := by
    by_contra hn
    exact hgood (Or.inr (Or.inl hn))
  have hmul : r (x : V) = p (q (x : V)) := by
    by_contra hn
    exact hgood (Or.inr (Or.inr hn))
  have hpq : p (q (x : V)) ∈ Z := hmul ▸ hr
  have hqvalue :
      ((completedRestriction q Z x : {v : V // v ∈ Z}) : V) =
        q (x : V) :=
    completedRestriction_apply_of_mem q Z x x.property hq
  apply Subtype.ext
  change
    ((completedRestriction r Z x : {v : V // v ∈ Z}) : V) =
      ((completedRestriction p Z
        (completedRestriction q Z x) : {v : V // v ∈ Z}) : V)
  calc
    ((completedRestriction r Z x : {v : V // v ∈ Z}) : V) =
        r (x : V) :=
      completedRestriction_apply_of_mem r Z x x.property hr
    _ = p (q (x : V)) := hmul
    _ = p ((completedRestriction q Z x : {v : V // v ∈ Z}) : V) := by
      rw [hqvalue]
    _ = ((completedRestriction p Z
          (completedRestriction q Z x) : {v : V // v ∈ Z}) : V) := by
      symm
      apply completedRestriction_apply_of_mem
      change p ((completedRestriction q Z x : {v : V // v ∈ Z}) : V) ∈ Z
      rw [hqvalue]
      exact hpq
end SoficGroups.KunActualTwicePrunedFirstFactorRootBad
