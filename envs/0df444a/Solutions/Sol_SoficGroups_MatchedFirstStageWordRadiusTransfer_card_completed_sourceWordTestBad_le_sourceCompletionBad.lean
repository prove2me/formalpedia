-- Prove2me | solution 1 for SoficGroups.MatchedFirstStageWordRadiusTransfer.card_completed_sourceWordTestBad_le_sourceCompletionBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/59570a82-14f0-4b0c-bef8-cee8b2cdeeba

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_mul_of_not_mem_sourceCompletionBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_ne_of_not_mem_sourceCompletionBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_commute_of_not_mem_sourceCompletionBad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedFirstStageWordRadiusTransfer
theorem _root_.solution
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (P : Finset V) :
    (SoficGroups.MatchedComponentExitBudget.sourceWordTestBad
      (fun i => SoficGroups.MatchedComponentCompletion.completedRestriction
        (σ i) P)
      (fun j => SoficGroups.MatchedComponentCompletion.completedRestriction
        (p j) P)
      F).card ≤
      (SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        σ p F P).card := by
  classical
  let σP : ι → Equiv.Perm {x : V // x ∈ P} := fun i =>
    SoficGroups.MatchedComponentCompletion.completedRestriction (σ i) P
  let pP : J → Equiv.Perm {x : V // x ∈ P} := fun j =>
    SoficGroups.MatchedComponentCompletion.completedRestriction (p j) P
  let W : Finset {x : V // x ∈ P} :=
    SoficGroups.MatchedComponentExitBudget.sourceWordTestBad σP pP F
  have hσP :
      ∀ i (x : V) (hx : x ∈ P) (_hi : σ i x ∈ P),
        ((σP i ⟨x, hx⟩ : {x : V // x ∈ P}) : V) = σ i x := by
    intro i x hx hi
    exact SoficGroups.MatchedComponentCompletion.completedRestriction_apply_of_mem
      (σ i) P x hx hi
  have hinject :
      W.map (Function.Embedding.subtype (fun x : V => x ∈ P)) ⊆
        SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          σ p F P := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    by_contra hnot
    have hwords : z ∈ W := hz
    simp [W, SoficGroups.MatchedComponentExitBudget.sourceWordTestBad,
      σP, pP] at hwords
    rcases hwords with hcomm | hmul | hsep
    · obtain ⟨i, j, hj, hfailure⟩ := hcomm
      exact hfailure
        (SoficGroups.MatchedComponentCompletion.completedRestriction_commute_of_not_mem_sourceCompletionBad
          σ p F P σP hσP hj i z hnot)
    · obtain ⟨j, hj, k, hk, hfailure⟩ := hmul
      apply hfailure
      simpa [Equiv.Perm.mul_apply] using
        SoficGroups.MatchedComponentCompletion.completedRestriction_mul_of_not_mem_sourceCompletionBad
          σ p F P hj hk z hnot
    · obtain ⟨j, hj, k, hk, hne, heq⟩ := hsep
      exact
        (SoficGroups.MatchedComponentCompletion.completedRestriction_ne_of_not_mem_sourceCompletionBad
          σ p F P hj hk hne z hnot) heq
  change W.card ≤ _
  calc
    W.card =
        (W.map (Function.Embedding.subtype (fun x : V => x ∈ P))).card :=
      (Finset.card_map _).symm
    _ ≤ (SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          σ p F P).card := Finset.card_le_card hinject
end SoficGroups.MatchedFirstStageWordRadiusTransfer
