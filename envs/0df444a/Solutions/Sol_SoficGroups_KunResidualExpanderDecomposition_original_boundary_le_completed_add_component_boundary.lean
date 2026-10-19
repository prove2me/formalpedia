-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.original_boundary_le_completed_add_component_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/a81e6b3a-a9d5-4020-8400-874402ebac15

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (A : Finset {x : V // x ∈ C}) :
    SoficGroups.boundary σ
        (A.map (Function.Embedding.subtype (fun x : V => x ∈ C))) ≤
      SoficGroups.boundary τ A +
        SoficGroups.boundary σ C := by
  classical
  let E : Finset V :=
    A.map (Function.Embedding.subtype (fun x : V => x ∈ C))
  change
    (∑ i : ι, (E.filter fun x => σ i x ∉ E).card) ≤
      (∑ i : ι, (A.filter fun x => τ i x ∉ A).card) +
        ∑ i : ι, (C.filter fun x => σ i x ∉ C).card
  calc
    (∑ i : ι, (E.filter fun x => σ i x ∉ E).card) ≤
      ∑ i : ι,
        ((A.filter fun x => τ i x ∉ A).card +
          (C.filter fun x => σ i x ∉ C).card) := by
        apply Finset.sum_le_sum
        intro i _
        let F : Finset V :=
          (A.filter fun x => τ i x ∉ A).map
            (Function.Embedding.subtype (fun x : V => x ∈ C))
        let D : Finset V := C.filter fun x => σ i x ∉ C
        have hsub :
            (E.filter fun x => σ i x ∉ E) ⊆ F ∪ D := by
          intro x hx
          obtain ⟨hxE, hxout⟩ := Finset.mem_filter.mp hx
          obtain ⟨z, hzA, rfl⟩ := Finset.mem_map.mp hxE
          by_cases hzinternal : σ i (z : V) ∈ C
          · have hnot : τ i z ∉ A := by
              intro hmem
              apply hxout
              apply Finset.mem_map.mpr
              refine ⟨τ i z, hmem, ?_⟩
              exact hτ i (z : V) z.property hzinternal
            apply Finset.mem_union_left
            exact Finset.mem_map.mpr
              ⟨z, Finset.mem_filter.mpr ⟨hzA, hnot⟩, rfl⟩
          · apply Finset.mem_union_right
            exact Finset.mem_filter.mpr ⟨z.property, hzinternal⟩
        calc
          (E.filter fun x => σ i x ∉ E).card ≤
              (F ∪ D).card :=
                Finset.card_le_card hsub
          _ ≤ F.card + D.card :=
                Finset.card_union_le F D
          _ = (A.filter fun x => τ i x ∉ A).card +
                (C.filter fun x => σ i x ∉ C).card := by
                  simp [F, D]
    _ = (∑ i : ι, (A.filter fun x => τ i x ∉ A).card) +
          ∑ i : ι, (C.filter fun x => σ i x ∉ C).card := by
            rw [Finset.sum_add_distrib]
end SoficGroups.KunResidualExpanderDecomposition
