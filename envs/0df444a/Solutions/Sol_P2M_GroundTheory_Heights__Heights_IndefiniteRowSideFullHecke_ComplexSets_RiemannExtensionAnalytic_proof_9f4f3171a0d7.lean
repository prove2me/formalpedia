-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_proof_9f4f3171a0d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:55.796967+00:00
-- url     : https://prove2.me/submissions/004146a3-6a92-4ae9-a995-725d5af78960

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_local_extension_09ab203d386c

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
open Metric Filter Topology Set Complex MeasureTheory
open scoped Real
noncomputable section
open RiemannExtensionAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace RiemannExtensionAnalytic
theorem _root_.solution : RiemannExtensionAnalytic.Statement := by
  intro k U g f hU hg hne hf hb
  have hloc := fun τ (hτ : τ ∈ U) => local_extension hU hg hne hf hb hτ
  choose! W hW Fl hFl hFlf using hloc
  have hdense : ∀ τ ∈ U, (𝓝[U ∩ {t | g t ≠ 0}] τ).NeBot := by
    intro τ hτ
    rw [← mem_closure_iff_nhdsWithin_neBot, _root_.mem_closure_iff]
    intro o ho hτo
    obtain ⟨t, ht, hgt⟩ := hne (o ∩ U) (ho.inter hU) inter_subset_right ⟨τ, hτo, hτ⟩
    exact ⟨t, ht.1, ht.2, hgt⟩
  set F : (Fin k → ℂ) → ℂ := fun τ => limUnder (𝓝[U ∩ {t | g t ≠ 0}] τ) f with hF
  have key : ∀ τ₀ ∈ U, ∀ᶠ τ in 𝓝 τ₀, F τ = Fl τ₀ τ := by
    intro τ₀ hτ₀
    filter_upwards [eventually_eventually_nhds.mpr (hW τ₀ hτ₀), hU.mem_nhds hτ₀] with τ hτW hτU
    have := hdense τ hτU
    have hc : ContinuousAt (Fl τ₀) τ := ((hFl τ₀ hτ₀).differentiableAt hτW).continuousAt
    refine Tendsto.limUnder_eq ?_
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hτW, self_mem_nhdsWithin] with t htW htO
    exact hFlf τ₀ hτ₀ t htW htO.1 htO.2
  refine ⟨F, fun τ₀ hτ₀ => ?_, fun τ hτ => ?_⟩
  · exact (((hFl τ₀ hτ₀).differentiableAt (hW τ₀ hτ₀)).congr_of_eventuallyEq
      (key τ₀ hτ₀)).differentiableWithinAt
  · rw [(key τ hτ.1).self_of_nhds]
    exact hFlf τ hτ.1 τ (mem_of_mem_nhds (hW τ hτ.1)) hτ.1 hτ.2
end RiemannExtensionAnalytic
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
