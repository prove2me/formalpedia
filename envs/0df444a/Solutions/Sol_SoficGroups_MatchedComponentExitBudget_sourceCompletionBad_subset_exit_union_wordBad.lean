-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.sourceCompletionBad_subset_exit_union_wordBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/6329505c-8d82-4ad3-9f55-0fd3425b9043

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedComponentExitBudget
theorem _root_.solution
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    SoficGroups.MatchedComponentCompletion.sourceCompletionBad σ p F Z ⊆
      (Finset.univ.biUnion fun i : ι =>
        Z.filter fun z => σ i z ∉ Z) ∪
      ((SoficGroups.CompressionCriterion.productTrackedTable F).biUnion
        fun j => Z.filter fun z => p j z ∉ Z) ∪
      (Finset.univ.biUnion fun i : ι =>
        (SoficGroups.CompressionCriterion.productTrackedTable F).biUnion
          fun j => Z.filter fun z => p j (σ i z) ∉ Z) ∪
      sourceWordTestBad σ p F := by
  classical
  intro x hx
  simp [SoficGroups.MatchedComponentCompletion.sourceCompletionBad,
    sourceWordTestBad] at hx ⊢
  rcases hx with hgen | hfactor | hcomm | hcomposite | hmul | hsep
  · obtain ⟨hxZ, i, hi⟩ := hgen
    exact Or.inl ⟨hxZ, i, hi⟩
  · obtain ⟨j, hj, hxZ, hexit⟩ := hfactor
    exact Or.inr (Or.inl ⟨j, hj, hxZ, hexit⟩)
  · obtain ⟨i, j, hj, _, hfailure⟩ := hcomm
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, hj, hfailure⟩)))
  · obtain ⟨i, j, hj, hxZ, hfailure⟩ := hcomposite
    exact Or.inr (Or.inr (Or.inl ⟨i, j, hj, hxZ, hfailure⟩))
  · obtain ⟨j, hj, k, hk, _, hfailure⟩ := hmul
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨j, hj, k, hk, hfailure⟩))))
  · obtain ⟨j, hj, k, hk, _, hne, hfailure⟩ := hsep
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨j, hj, k, hk, hne, hfailure⟩))))
end SoficGroups.MatchedComponentExitBudget
