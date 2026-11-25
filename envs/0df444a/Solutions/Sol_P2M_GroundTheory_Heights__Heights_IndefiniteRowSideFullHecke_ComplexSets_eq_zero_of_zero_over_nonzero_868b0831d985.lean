-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_zero_over_nonzero_868b0831d985
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:32:13.30136+00:00
-- url     : https://prove2.me/submissions/98713d8b-b9d3-45ab-8671-707e6ef9764b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral

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
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {k : ℕ} (Z W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (D : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → ℂ) (hWo : IsOpen W)
    (hDo : IsOpen D) (hgne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, g t ≠ 0)
    (hopen : ∀ z ∈ Z ∩ W, ∀ ε > 0, A '' (Z ∩ Metric.ball z ε) ∈ 𝓝 (A z)) {x : σ → ℂ} (hx : x ∈ Z ∩ W)
    (hAx : A x ∈ D) (Ψ : (σ → ℂ) → ℂ) (hΨ : ContinuousAt Ψ x) (V₀ : Set (σ → ℂ)) (hV₀ : V₀ ∈ 𝓝 x)
    (h0 : ∀ z ∈ Z ∩ W ∩ V₀, A z ∈ D → g (A z) ≠ 0 → Ψ z = 0) : Ψ x = 0 := by
  by_contra hne
  have hev : ∀ᶠ z in 𝓝 x, z ∈ V₀ ∧ z ∈ W ∧ A z ∈ D ∧ Ψ z ≠ 0 :=
    Filter.Eventually.and (hV₀ : ∀ᶠ z in 𝓝 x, z ∈ V₀) (Filter.Eventually.and
      (hWo.mem_nhds hx.2 : ∀ᶠ z in 𝓝 x, z ∈ W) (Filter.Eventually.and
        (A.continuous.continuousAt.preimage_mem_nhds (hDo.mem_nhds hAx) : ∀ᶠ z in 𝓝 x, A z ∈ D)
        (hΨ.eventually_ne hne)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hn : A '' (Z ∩ Metric.ball x ε) ∩ D ∈ 𝓝 (A x) :=
    Filter.inter_mem (hopen x hx ε hε) (hDo.mem_nhds hAx)
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.1 hn
  obtain ⟨t, htV, hgt⟩ := hgne V hVo (fun v hv => (hVsub hv).2) ⟨_, hxV⟩
  obtain ⟨⟨z, ⟨hzZ, hzb⟩, rfl⟩, -⟩ := hVsub htV
  obtain ⟨hzV, hzW, hzD, hΨz⟩ := hball z hzb
  exact hΨz (h0 z ⟨⟨hzZ, hzW⟩, hzV⟩ hzD hgt)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
