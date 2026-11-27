-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormWindow_proof_19406b950b1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:59:45.914474+00:00
-- url     : https://prove2.me/submissions/79c1e873-1802-4c60-b497-e08974220441

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormWindow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormWindow

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
namespace PrimitiveFormWindow
theorem _root_.solution : PrimitiveFormWindow.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hp hsep hrel
  obtain ⟨N₀, k, f, hN₀o, hwN₀, hfa, hXN⟩ := hX
  obtain ⟨W₀, hW₀, hW₀iso⟩ := hiso
  have hev := (show ∀ᶠ z in 𝓝 w, z ∈ N₀ from hN₀o.mem_nhds hwN₀).and
    ((show ∀ᶠ z in 𝓝 w, z ∈ W₀ from hW₀).and (hp.and (Filter.eventually_all.2 hrel)))
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hev
  set K : Set (σ → ℂ) := Metric.sphere w ε ∩ (fun z i => f i z) ⁻¹' {0} with hK
  have hsN : Metric.sphere w ε ⊆ N₀ := fun z hz => (hεs (Metric.sphere_subset_closedBall hz)).1
  have hKc : IsCompact K := by
    refine (isCompact_sphere w ε).of_isClosed_subset ?_ Set.inter_subset_left
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_sphere isClosed_singleton
    exact continuousOn_pi.2 fun i => ((hfa i).continuousOn).mono hsN
  have hKX : ∀ z ∈ K, z ∈ X := by
    intro z hz
    have : z ∈ X ∩ N₀ := by
      rw [hXN]
      refine ⟨hsN hz.1, fun i => ?_⟩
      have := congrFun (Set.mem_singleton_iff.1 hz.2) i
      simpa using this
    exact this.1
  have hXK : ∀ z ∈ X, z ∈ Metric.sphere w ε → z ∈ K := by
    intro z hzX hzs
    refine ⟨hzs, ?_⟩
    have : z ∈ X ∩ N₀ := ⟨hzX, hsN hzs⟩
    rw [hXN] at this
    exact Set.mem_singleton_iff.2 (funext this.2)
  have hAK : A w ∉ A '' K := by
    rintro ⟨z, hzK, hAz⟩
    have hzw := (hεs (Metric.sphere_subset_closedBall hzK.1)).2.1
    have hzeq := hW₀iso z ⟨hKX z hzK, hzw⟩ hAz
    have h1 := hzK.1
    rw [hzeq, Metric.mem_sphere, dist_self] at h1
    exact hε.ne h1
  have hclo : IsClosed (A '' K) := (hKc.image A.continuous).isClosed
  have hev2 := (show ∀ᶠ y in 𝓝 (A w), y ∈ (A '' K)ᶜ from hclo.isOpen_compl.mem_nhds hAK).and
    ((Filter.eventually_all.2 fun j => (ha j).eventually_analyticAt).and
      (hδ.eventually_analyticAt.and
        ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
          (hq i j).eventually_analyticAt).and hsep)))
  obtain ⟨ρ, hρ, hρs⟩ := Metric.nhds_basis_ball.eventually_iff.1 hev2
  refine ⟨Metric.ball w ε, Metric.ball (A w) ρ, N₀, k, f, Metric.isOpen_ball, Metric.mem_ball_self hε,
    Metric.isOpen_ball, convex_ball _ _, Metric.mem_ball_self hρ, hN₀o, ?_, hfa, hXN, ?_, ?_, ?_,
    fun j y hy => (hρs hy).2.1 j, fun y hy => (hρs hy).2.2.1, fun i j y hy => (hρs hy).2.2.2.1 i j,
    fun y hy => (hρs hy).2.2.2.2⟩
  · rw [closure_ball w hε.ne']
    exact fun z hz => (hεs hz).1
  · rintro z ⟨hzX, hzc⟩ hzB
    rw [closure_ball w hε.ne'] at hzc
    rcases (Metric.mem_closedBall.1 hzc).lt_or_eq with h | h
    · exact Metric.mem_ball.2 h
    · exact absurd ⟨z, hXK z hzX (Metric.mem_sphere.2 h), rfl⟩ (hρs hzB).1
  · rintro z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.1 hzX
  · rintro i z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.2 i hzX
end PrimitiveFormWindow
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
