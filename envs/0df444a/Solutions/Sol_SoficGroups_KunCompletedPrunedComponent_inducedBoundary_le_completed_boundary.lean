-- Prove2me | solution 1 for SoficGroups.KunCompletedPrunedComponent.inducedBoundary_le_completed_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/d5d8baab-2225-409c-8c94-6c53f7e44187

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedPrunedComponent
open scoped BigOperators
namespace SoficGroups.KunCompletedPrunedComponent
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B Z : Finset V)
    (hZ : Z = Finset.univ \ B)
    (τ : ι → Equiv.Perm {x : V // x ∈ Z})
    (hτ : ∀ i (x : V) (hx : x ∈ Z) (_hy : σ i x ∈ Z),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ Z}) : V) = σ i x)
    (A : Finset {x : V // x ∈ Z}) :
    SoficGroups.inducedBoundary σ B
        (A.map (Function.Embedding.subtype (fun x : V => x ∈ Z))) ≤
      SoficGroups.boundary τ A := by
  classical
  let E : Finset V :=
    A.map (Function.Embedding.subtype (fun x : V => x ∈ Z))
  have hmemZ (x : V) : x ∈ Z ↔ x ∉ B := by
    rw [hZ]
    simp
  change
    (∑ i : ι,
      (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card) ≤
      ∑ i : ι, (A.filter fun x => τ i x ∉ A).card
  apply Finset.sum_le_sum
  intro i _
  have hsub :
      (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E) ⊆
        (A.filter fun x => τ i x ∉ A).map
          (Function.Embedding.subtype (fun x : V => x ∈ Z)) := by
    intro x hx
    obtain ⟨hxE, hxB, hxout⟩ := Finset.mem_filter.mp hx
    obtain ⟨z, hzA, rfl⟩ := Finset.mem_map.mp hxE
    have himage : σ i (z : V) ∈ Z :=
      (hmemZ (σ i (z : V))).2 hxB
    have hnot : τ i z ∉ A := by
      intro hmem
      apply hxout
      exact Finset.mem_map.mpr
        ⟨τ i z, hmem, hτ i (z : V) z.property himage⟩
    exact Finset.mem_map.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hzA, hnot⟩, rfl⟩
  calc
    (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card ≤
        ((A.filter fun x => τ i x ∉ A).map
          (Function.Embedding.subtype (fun x : V => x ∈ Z))).card :=
      Finset.card_le_card hsub
    _ = (A.filter fun x => τ i x ∉ A).card :=
      Finset.card_map _
end SoficGroups.KunCompletedPrunedComponent
