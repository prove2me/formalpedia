-- Prove2me | solution 1 for SoficGroups.KunActualFirstStageReferenceExpansion.completed_actual_component_additive_expansion_of_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/47546ed8-911a-4e6b-95ac-4918e96fb1f1

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_complement
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_original_boundary_le_completed_add_component_boundary
import Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_boundary_complement
import Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_componentGeneratorDisagreement_comm
import Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_boundary_le_boundary_add_componentGeneratorDisagreement

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunActualFirstStageReferenceExpansion
theorem _root_.solution
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σref σact : ι → Equiv.Perm V) (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σact i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σact i x)
    (γ : ℝ)
    (hexpand : ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary σref E : ℝ)) :
    ∀ E : Finset {x : V // x ∈ C},
      γ * min (E.card : ℝ) ((C.card : ℝ) - E.card) -
        ((SoficGroups.boundary σref C : ℝ) +
          2 * (componentGeneratorDisagreement C σref σact : ℝ)) ≤
        (SoficGroups.boundary τ E : ℝ) := by
  classical
  have hhalf (E : Finset {x : V // x ∈ C})
      (hE : 2 * E.card ≤ C.card) :
      γ * (E.card : ℝ) -
        ((SoficGroups.boundary σref C : ℝ) +
          2 * (componentGeneratorDisagreement C σref σact : ℝ)) ≤
        (SoficGroups.boundary τ E : ℝ) := by
    let D : Finset V :=
      E.map (Function.Embedding.subtype (fun x : V => x ∈ C))
    have hDC : D ⊆ C := by
      intro x hx
      exact Finset.property_of_mem_map_subtype E hx
    have hcard : D.card = E.card := by
      dsimp [D]
      exact Finset.card_map _
    have hhalfD : 2 * D.card ≤ C.card := by
      simpa only [hcard] using hE
    have hreference := hexpand D hDC hhalfD
    rw [hcard] at hreference
    have hchanged :=
      boundary_le_boundary_add_componentGeneratorDisagreement
        σref σact C D hDC
    have hcompleted :=
      SoficGroups.KunResidualExpanderDecomposition.original_boundary_le_completed_add_component_boundary
        σact C τ hτ E
    have hcomponent :=
      boundary_le_boundary_add_componentGeneratorDisagreement
        σact σref C C (Finset.Subset.refl C)
    rw [componentGeneratorDisagreement_comm C σact σref] at hcomponent
    have hchangedR :
        (SoficGroups.boundary σref D : ℝ) ≤
          (SoficGroups.boundary σact D : ℝ) +
            (componentGeneratorDisagreement C σref σact : ℝ) := by
      exact_mod_cast hchanged
    have hcompletedR :
        (SoficGroups.boundary σact D : ℝ) ≤
          (SoficGroups.boundary τ E : ℝ) +
            (SoficGroups.boundary σact C : ℝ) := by
      change
        ((SoficGroups.boundary σact
          (E.map (Function.Embedding.subtype
            (fun x : V => x ∈ C))) : ℕ) : ℝ) ≤ _
      exact_mod_cast hcompleted
    have hcomponentR :
        (SoficGroups.boundary σact C : ℝ) ≤
          (SoficGroups.boundary σref C : ℝ) +
            (componentGeneratorDisagreement C σref σact : ℝ) := by
      exact_mod_cast hcomponent
    linarith
  intro E
  by_cases hE : 2 * E.card ≤ C.card
  · have hreal : (2 : ℝ) * (E.card : ℝ) ≤ (C.card : ℝ) := by
      exact_mod_cast hE
    rw [min_eq_left (by linarith)]
    exact hhalf E hE
  · let D : Finset {x : V // x ∈ C} := Finset.univ \ E
    have hcard : D.card + E.card = C.card := by
      dsimp [D]
      have h :=
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
      simpa using h
    have hhalfD : 2 * D.card ≤ C.card := by
      omega
    have hsmall := hhalf D hhalfD
    have hrealD : (D.card : ℝ) = (C.card : ℝ) - (E.card : ℝ) := by
      have hreal :
          (D.card : ℝ) + (E.card : ℝ) = (C.card : ℝ) := by
        exact_mod_cast hcard
      linarith
    have hrealE : (C.card : ℝ) < 2 * (E.card : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge hE
    rw [min_eq_right (by linarith)]
    rw [hrealD] at hsmall
    have hcomplement :
        SoficGroups.boundary τ D = SoficGroups.boundary τ E := by
      simpa only [D] using
        SoficGroups.KunResidualExpanderDecomposition.boundary_complement τ E
    rw [hcomplement] at hsmall
    exact hsmall
end SoficGroups.KunActualFirstStageReferenceExpansion
