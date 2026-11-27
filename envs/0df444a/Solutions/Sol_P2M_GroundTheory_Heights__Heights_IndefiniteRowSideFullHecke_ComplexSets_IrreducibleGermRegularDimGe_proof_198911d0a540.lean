-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IrreducibleGermRegularDimGe_proof_198911d0a540
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:40.328135+00:00
-- url     : https://prove2.me/submissions/0d70c5e8-23c2-4f87-87de-dc6154d00d46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermRegularDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetsDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermRegularDimGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ImplicitCurve_proof_a85e02a226ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicFibreInfinite_proof_2a14330f99ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace IrreducibleGermRegularDimGe
theorem _root_.solution (hS : FiniteProjectionSheetsDense.Statement) :
    IrreducibleGermRegularDimGe.Statement := by
  intro σ _ X w d A hX hirr hiso hnd
  obtain ⟨N, hN, hsub⟩ := hS σ X w d A hX hirr hiso hnd
  refine ⟨N, hN, ?_⟩
  intro x hx e A' O V g hO hV hxV hg hleft hXV
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y, hyV, hyX, O₁, V₁, g₁, hO₁, hV₁, hyV₁, hg₁, hleft₁, hXV₁⟩ :=
    mem_closure_iff.1 (hsub hx) V hV hxV
  have hy : y ∈ g₁ '' O₁ := hXV₁ ▸ ⟨hyX, hyV₁⟩
  obtain ⟨t₀, ht₀, rfl⟩ := hy
  set U : Set (Fin d → ℂ) := O₁ ∩ g₁ ⁻¹' V with hUdef
  have hU : IsOpen U := hg₁.continuousOn.isOpen_inter_preimage hO₁ hV
  have hUne : U.Nonempty := ⟨t₀, ht₀, hyV⟩
  have hdiff : DifferentiableOn ℂ (fun t => A' (g₁ t)) U :=
    A'.differentiable.comp_differentiableOn (hg₁.differentiableOn.mono Set.inter_subset_left)

  have hmem : ∀ t ∈ U, ∃ u ∈ O, g₁ t = g u := by
    intro t ht
    have h1 : g₁ t ∈ X ∩ V₁ := hXV₁ ▸ Set.mem_image_of_mem g₁ ht.1
    have h2 : g₁ t ∈ X ∩ V := ⟨h1.1, ht.2⟩
    rw [hXV] at h2
    obtain ⟨u, hu, hgu⟩ := h2
    exact ⟨u, hu, hgu.symm⟩
  obtain ⟨z, hz⟩ := HolomorphicFibreInfinite.proof d e U (fun t => A' (g₁ t)) hlt hU hUne hdiff
  apply hz
  refine Set.Subsingleton.finite ?_
  intro t₁ ht₁ t₂ ht₂
  obtain ⟨u₁, hu₁, hg1⟩ := hmem t₁ ht₁.1
  obtain ⟨u₂, hu₂, hg2⟩ := hmem t₂ ht₂.1
  have hz1 : A' (g₁ t₁) = z := ht₁.2
  have hz2 : A' (g₁ t₂) = z := ht₂.2
  rw [hg1, hleft u₁ hu₁] at hz1
  rw [hg2, hleft u₂ hu₂] at hz2
  have hgg : g₁ t₁ = g₁ t₂ := by rw [hg1, hg2, hz1, hz2]
  rw [← hleft₁ t₁ ht₁.1.1, ← hleft₁ t₂ ht₂.1.1, hgg]
end IrreducibleGermRegularDimGe
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
