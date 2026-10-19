-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.completed_component_additive_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/81a9cead-28a5-4b04-a07b-52b93de6d21f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_complement
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_original_boundary_le_completed_add_component_boundary

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
    (γ : ℝ)
    (hexpand : ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ)) :
    ∀ A : Finset {x : V // x ∈ C},
      γ * min (A.card : ℝ) ((C.card : ℝ) - A.card) -
          (SoficGroups.boundary σ C : ℝ) ≤
        (SoficGroups.boundary τ A : ℝ) := by
  classical
  have hhalf (A : Finset {x : V // x ∈ C})
      (hA : 2 * A.card ≤ C.card) :
      γ * (A.card : ℝ) -
          (SoficGroups.boundary σ C : ℝ) ≤
        (SoficGroups.boundary τ A : ℝ) := by
    let E : Finset V :=
      A.map (Function.Embedding.subtype (fun x : V => x ∈ C))
    have hEC : E ⊆ C := by
      intro x hx
      exact Finset.property_of_mem_map_subtype A hx
    have hEcard : E.card = A.card := by
      dsimp [E]
      exact Finset.card_map _
    have hEhalf : 2 * E.card ≤ C.card := by
      simpa only [hEcard] using hA
    have hsource := hexpand E hEC hEhalf
    have hboundary :
        (SoficGroups.boundary σ E : ℝ) ≤
          (SoficGroups.boundary τ A : ℝ) +
            (SoficGroups.boundary σ C : ℝ) := by
      have h :=
        original_boundary_le_completed_add_component_boundary
          σ C τ hτ A
      change
        ((SoficGroups.boundary σ E : ℕ) : ℝ) ≤ _
      exact_mod_cast h
    rw [hEcard] at hsource
    linarith
  intro A
  by_cases hA : 2 * A.card ≤ C.card
  · have hreal :
        (2 : ℝ) * (A.card : ℝ) ≤ (C.card : ℝ) := by
      exact_mod_cast hA
    rw [min_eq_left (by linarith)]
    exact hhalf A hA
  · let D : Finset {x : V // x ∈ C} := Finset.univ \ A
    have hcard :
        D.card + A.card = C.card := by
      dsimp [D]
      have h :=
        Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ A)
      simpa using h
    have hDhalf : 2 * D.card ≤ C.card := by
      omega
    have hD := hhalf D hDhalf
    have hDreal :
        (D.card : ℝ) = (C.card : ℝ) - (A.card : ℝ) := by
      have hreal :
          (D.card : ℝ) + (A.card : ℝ) = (C.card : ℝ) := by
        exact_mod_cast hcard
      linarith
    have hreal :
        (C.card : ℝ) < 2 * (A.card : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge hA
    rw [min_eq_right (by linarith)]
    rw [hDreal] at hD
    have hcomplement :
        SoficGroups.boundary τ D =
          SoficGroups.boundary τ A := by
      simpa only [D] using boundary_complement τ A
    rw [hcomplement] at hD
    exact hD
end SoficGroups.KunResidualExpanderDecomposition
