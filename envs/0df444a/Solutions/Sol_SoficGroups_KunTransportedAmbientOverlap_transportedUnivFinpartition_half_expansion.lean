-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.transportedUnivFinpartition_half_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/4946c8e8-318a-4ee6-859a-8f763fb1464d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_boundary_conjugate_map

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunTransportedAmbientOverlap
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V) (T : Equiv.Perm V)
    (gamma : ℝ)
    (hexp : ∀ C ∈ Q.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        gamma * (E.card : ℝ) ≤
          (SoficGroups.boundary σ E : ℝ)) :
    ∀ C ∈ (SoficGroups.transportedUnivFinpartition Q T).parts,
      ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i => T * σ i * T⁻¹) E : ℝ) := by
  classical
  intro C hC
  rw [SoficGroups.transportedUnivFinpartition_parts] at hC
  obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
  intro E hE hhalf
  let E₀ : Finset V := E.map T.symm.toEmbedding
  have hrecovery : E₀.map T.toEmbedding = E := by
    simp [E₀, Finset.map_map]
  have hsub : E₀ ⊆ C₀ := by
    apply (Finset.map_subset_map (f := T.toEmbedding)).mp
    simpa only [hrecovery] using hE
  have hhalf₀ : 2 * E₀.card ≤ C₀.card := by
    simpa [E₀] using hhalf
  have hsource := hexp C₀ hC₀ E₀ hsub hhalf₀
  have hboundary :=
    boundary_conjugate_map σ T E₀
  calc
    gamma * (E.card : ℝ) = gamma * (E₀.card : ℝ) := by
      simp [E₀]
    _ ≤ (SoficGroups.boundary σ E₀ : ℝ) := hsource
    _ = (SoficGroups.boundary
      (fun i => T * σ i * T⁻¹)
        (E₀.map T.toEmbedding) : ℝ) := by
      exact_mod_cast hboundary.symm
    _ = (SoficGroups.boundary
      (fun i => T * σ i * T⁻¹) E : ℝ) := by
      rw [hrecovery]
end SoficGroups.KunTransportedAmbientOverlap
