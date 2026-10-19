-- Prove2me | solution 1 for SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_additive_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/792bb43c-641e-4b2b-8606-c381cd22c8f7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_componentVertexMidrank_nonneg
import Theorems.Thm_SoficGroups_componentVertexMidrank_le_one
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_componentVertexMidrank_finiteVariance_eq
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_completed_component_additive_expansion
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_additive_permutation_finiteVariance
import Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_sum_completed_component_real_variation_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunGlobalActualAdditiveMidrankVariance
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunGlobalActualAdditiveMidrankVariance
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (P : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V)
    (τ : (C : Finset V) → ι → Equiv.Perm {x : V // x ∈ C})
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hτ : ∀ C ∈ P.parts, ∀ i (x : V)
      (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ C i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (hexpand : ∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ))
    (b : V → ℤ) :
    2 * γ *
        (∑ C ∈ P.parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C b)) ≤
      SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
        σ (SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank P b) +
        5 * (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) := by
  classical
  let f : V → ℝ :=
    SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank P b
  have hf0 (x : V) : 0 ≤ f x :=
    SoficGroups.componentVertexMidrank_nonneg (P.part x) b x
  have hf1 (x : V) : f x ≤ 1 :=
    SoficGroups.componentVertexMidrank_le_one (P.part x) b x
  have hcomponent (C : Finset V) (hC : C ∈ P.parts) :
      2 * γ * (C.card : ℝ) *
          SoficGroups.midrankVariance
            (SoficGroups.componentRankMassList C b) ≤
        SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
          (τ C) (fun x : {x : V // x ∈ C} => f (x : V)) +
          4 * (SoficGroups.boundary σ C : ℝ) := by
    have hCne : C.Nonempty := P.nonempty_of_mem_parts hC
    letI : Nonempty {x : V // x ∈ C} :=
      ⟨⟨hCne.choose, hCne.choose_spec⟩⟩
    have hrestrict :
        (fun x : {x : V // x ∈ C} => f (x : V)) =
          (fun x : {x : V // x ∈ C} =>
            SoficGroups.componentVertexMidrank C b (x : V)) := by
      funext x
      change
        SoficGroups.componentVertexMidrank (P.part (x : V)) b (x : V) =
          SoficGroups.componentVertexMidrank C b (x : V)
      rw [P.part_eq_of_mem hC x.property]
    have hcut (E : Finset {x : V // x ∈ C}) :
        γ * min (E.card : ℝ)
            ((Fintype.card {x : V // x ∈ C} : ℝ) - E.card) ≤
          (SoficGroups.boundary (τ C) E : ℝ) +
            (SoficGroups.boundary σ C : ℝ) := by
      have h :=
        SoficGroups.KunResidualExpanderDecomposition.completed_component_additive_expansion
          σ C (τ C) (hτ C hC) γ (hexpand C hC) E
      have h' :
          γ * min (E.card : ℝ) ((C.card : ℝ) - E.card) ≤
            (SoficGroups.boundary (τ C) E : ℝ) +
              (SoficGroups.boundary σ C : ℝ) := by
        linarith
      simpa only [Fintype.card_coe] using h'
    have hp :=
      SoficGroups.KunAdditiveMedianPoincare.additive_permutation_finiteVariance
        (τ C) γ (SoficGroups.boundary σ C : ℝ)
        hγ (Nat.cast_nonneg _) hcut
        (fun x : {x : V // x ∈ C} =>
          SoficGroups.componentVertexMidrank C b (x : V))
        (fun x => SoficGroups.componentVertexMidrank_nonneg C b (x : V))
        (fun x => SoficGroups.componentVertexMidrank_le_one C b (x : V))
    rw [Fintype.card_coe,
      SoficGroups.ComponentMidrankVariance.componentVertexMidrank_finiteVariance_eq
        C b hCne] at hp
    rw [← hrestrict] at hp
    simpa only
      [SoficGroups.KunAdditiveMedianPoincare.permutationRealVariation,
       SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation]
      using hp
  have hsummed :
      2 * γ *
          (∑ C ∈ P.parts,
            (C.card : ℝ) *
              SoficGroups.midrankVariance
                (SoficGroups.componentRankMassList C b)) ≤
        (∑ C ∈ P.parts,
          SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
            (τ C) (fun x : {x : V // x ∈ C} => f (x : V))) +
          4 * (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) := by
    calc
      2 * γ *
          (∑ C ∈ P.parts,
            (C.card : ℝ) *
              SoficGroups.midrankVariance
                (SoficGroups.componentRankMassList C b)) =
        ∑ C ∈ P.parts,
          2 * γ * (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C b) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro C _
              ring
      _ ≤ ∑ C ∈ P.parts,
          (SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
            (τ C) (fun x : {x : V // x ∈ C} => f (x : V)) +
            4 * (SoficGroups.boundary σ C : ℝ)) := by
              apply Finset.sum_le_sum
              intro C hC
              exact hcomponent C hC
      _ = (∑ C ∈ P.parts,
          SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
            (τ C) (fun x : {x : V // x ∈ C} => f (x : V))) +
          4 * (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hcompletion :=
    SoficGroups.KunCompletedComponentMidrankVariation.sum_completed_component_real_variation_le
      P σ τ hτ f hf0 hf1
  change
    2 * γ *
        (∑ C ∈ P.parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C b)) ≤
      SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
        σ f +
        5 * (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ))
  linarith
end SoficGroups.KunGlobalActualAdditiveMidrankVariance
