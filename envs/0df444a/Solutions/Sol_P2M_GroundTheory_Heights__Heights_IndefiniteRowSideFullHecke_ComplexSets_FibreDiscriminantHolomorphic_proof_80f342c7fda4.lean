-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_proof_80f342c7fda4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:34.293004+00:00
-- url     : https://prove2.me/submissions/e12231f0-5be5-4fd3-94e2-c9bdd5668aca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_bound_pairs_7ea5a7f18a7c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_norm_fibreDiscr_le_b1f5bc30d339
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_continuousAt_of_count_eq_8458b74112a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_continuousAt_of_count_ne_ca785de3f3fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_analyticAt_of_sections_46f0407d8b3a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_analyticOnNhd_of_differentiableOn_c966cce3f6fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_proof_9f4f3171a0d7
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
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
theorem _root_.solution : FibreDiscriminantHolomorphic.Statement := by
  intro σ _ Y d A D N l hD _ hproper hopen hcov y₀ hy₀
  obtain ⟨U, g, hU, hy₀U, hUD, hg, hgdense, hgN⟩ := hcov.2 y₀ hy₀
  have hle := hcov.1
  have hcont : ∀ y ∈ D, ContinuousAt (fibreDiscr Y A l N) y := fun y hy => by
    by_cases h : {x | x ∈ Y ∧ A x = y}.encard = N
    · exact continuousAt_of_count_eq l hD hopen hle hy h
    · exact continuousAt_of_count_ne l hD hproper hle hy h
  have hdiff : DifferentiableOn ℂ (fibreDiscr Y A l N) (U ∩ {t | g t ≠ 0}) := fun t ht =>
    (analyticAt_of_sections l hD hle (hUD ht.1) (hgN t ht.1 ht.2).1
      (hgN t ht.1 ht.2).2).differentiableAt.differentiableWithinAt
  have hbdd : ∀ τ ∈ U, ∃ M ∈ 𝓝 τ,
      Bornology.IsBounded (fibreDiscr Y A l N '' (M ∩ U ∩ {t | g t ≠ 0})) := by
    intro τ hτ
    obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hD τ (hUD hτ)
    have hKD : closedBall τ (ρ / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hρD
    obtain ⟨C, hC1, hC⟩ := exists_bound_pairs l (hproper _ hKD (isCompact_closedBall τ (ρ / 2)))
    refine ⟨closedBall τ (ρ / 2), closedBall_mem_nhds τ (by linarith), ?_⟩
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C ^ (N * N), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact norm_fibreDiscr_le l hC1 hC ht.1.1
  obtain ⟨F, hF, hFf⟩ :=
    RiemannExtensionAnalytic.proof d U g (fibreDiscr Y A l N) hU hg.differentiableOn hgdense hdiff hbdd
  have hclos : U ⊆ closure (U ∩ {t | g t ≠ 0}) := by
    intro t ht
    rw [_root_.mem_closure_iff]
    intro o ho hto
    obtain ⟨s, hs, hgs⟩ := hgdense (o ∩ U) (ho.inter hU) inter_subset_right ⟨t, hto, ht⟩
    exact ⟨s, hs.1, hs.2, hgs⟩
  have hEq : EqOn F (fibreDiscr Y A l N) U := Set.EqOn.of_subset_closure hFf hF.continuousOn
    (fun t ht => (hcont t (hUD ht)).continuousWithinAt) inter_subset_left hclos
  have hfU : DifferentiableOn ℂ (fibreDiscr Y A l N) U := hF.congr fun t ht => (hEq ht).symm
  exact RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hU hfU y₀ hy₀U
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
