-- Prove2me | solution 1 for SoficGroups.KunCompletedComponentMidrankVariation.sum_completed_component_real_variation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/d7fd2707-6d74-4e5f-a58d-4a625d05df42

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_sum_partition_parts_eq
import Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_completed_component_real_variation_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedComponentMidrankVariation
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunCompletedComponentMidrankVariation
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (P : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V)
    (τ : (C : Finset V) → ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ C ∈ P.parts, ∀ i (x : V)
      (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ C i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (f : V → ℝ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    (∑ C ∈ P.parts,
      permutationRealVariation (τ C) (fun x => f (x : V))) ≤
      permutationRealVariation σ f +
        ∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ) := by
  classical
  have hparts :
      (∑ C ∈ P.parts, ∑ i : ι, ∑ x ∈ C,
        |f (σ i x) - f x|) =
        permutationRealVariation σ f := by
    unfold permutationRealVariation
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_partition_parts_eq P
      (fun x : V => |f (σ i x) - f x|)
  calc
    (∑ C ∈ P.parts,
      permutationRealVariation (τ C) (fun x => f (x : V))) ≤
        ∑ C ∈ P.parts,
          ((∑ i : ι, ∑ x ∈ C, |f (σ i x) - f x|) +
            (SoficGroups.boundary σ C : ℝ)) := by
          apply Finset.sum_le_sum
          intro C hC
          exact completed_component_real_variation_le
            σ C (τ C) (hτ C hC) f hf0 hf1
    _ = permutationRealVariation σ f +
          ∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ) := by
          rw [Finset.sum_add_distrib, hparts]
end SoficGroups.KunCompletedComponentMidrankVariation
