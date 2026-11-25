-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_extend_across_centre_fff121512849
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:50.526119+00:00
-- url     : https://prove2.me/submissions/cd8f16bf-456d-496a-9300-54896f19413d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCoverCycles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCentredDiscCoverCurve

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
open Topology Filter Metric Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) {δ : ℝ} {k : ℕ} {φ : ℂ → σ → ℂ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 1 ≤ k) (hφd : DifferentiableOn ℂ φ (ball 0 δ \ {0})) (hφi : Set.InjOn φ (ball 0 δ \ {0}))
    (hφY : ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k) :
    ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
      DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y := by
  obtain ⟨hwY, -, hmaps, huniq, -, hprop, -⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  set r := min δ (ρ / 2) with hr
  have hr0 : 0 < r := lt_min hδ (half_pos hρ)
  have hrδ : ball (0 : ℂ) r \ {0} ⊆ ball 0 δ \ {0} :=
    Set.sdiff_subset_sdiff_left (ball_subset_ball (min_le_left _ _))
  have hK : IsCompact {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hprop _ (closedBall_subset_ball (half_lt_self hρ)) (isCompact_closedBall _ _)
  have hφK : ∀ s ∈ ball (0 : ℂ) r \ {0}, φ s ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} := by
    intro s hs
    obtain ⟨hY', hp⟩ := hφY s (hrδ hs)
    refine ⟨hY', ?_⟩
    rw [mem_closedBall, hp, dist_eq_norm, add_sub_cancel_left, norm_pow]
    have h1 : ‖s‖ < r := mem_ball_zero_iff.1 hs.1
    calc ‖s‖ ^ k ≤ ‖s‖ :=
          pow_le_of_le_one (norm_nonneg _) (h1.le.trans ((min_le_left _ _).trans hδ1)) (by omega)
      _ ≤ ρ / 2 := h1.le.trans (min_le_right _ _)
  have hbdd : BddAbove (norm ∘ φ '' (ball 0 r \ {0})) := by
    refine (hK.image continuous_norm).bddAbove.mono ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨φ s, hφK s hs, rfl⟩
  have hF := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr0) (hφd.mono hrδ) hbdd
  set ℓ := limUnder (𝓝[≠] (0 : ℂ)) φ with hℓdef
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ∈ ball (0 : ℂ) r \ {0} := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds 0 hr0)] with s h1 h2
    exact ⟨h2, h1⟩
  have hlim : Tendsto φ (𝓝[≠] 0) (𝓝 ℓ) := by
    have hc := (hF.continuousOn.continuousAt (ball_mem_nhds 0 hr0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [Function.update_self] at hc
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Function.update_of_ne hs _ _
  have hℓK : ℓ ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hK.isClosed.mem_of_tendsto hlim (hev.mono hφK)
  have hpℓ : p ℓ = p w := by
    have h1 : Tendsto (fun s => p (φ s)) (𝓝[≠] 0) (𝓝 (p ℓ)) := (p.continuous.tendsto ℓ).comp hlim
    have h2 : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝[≠] 0) (𝓝 (p w)) := by
      have : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝 0) (𝓝 (p w + 0 ^ k)) :=
        (continuous_const.add (continuous_pow k)).tendsto 0
      rw [zero_pow (by omega), add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (h1.congr' ?_) h2
    filter_upwards [hev] with s hs
    exact (hφY s (hrδ hs)).2
  have hℓ : ℓ = w := huniq ℓ hℓK.1 hpℓ
  refine ⟨r, hr0, Function.update φ 0 w, ?_, ?_, Function.update_self _ _ _, ?_⟩
  · rw [← hℓ]
    exact hF
  · have hoff : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → Function.update φ 0 w s ≠ w := by
      intro s hs h0 heq
      rw [Function.update_of_ne h0] at heq
      have := (hφY s (hrδ ⟨hs, h0⟩)).2
      rw [heq] at this
      exact pow_ne_zero k h0 (by linear_combination -this)
    intro s hs s' hs' hss'
    by_cases h0 : s = 0 <;> by_cases h0' : s' = 0
    · rw [h0, h0']
    · subst h0
      rw [Function.update_self] at hss'
      exact absurd hss'.symm (hoff s' hs' h0')
    · subst h0'
      rw [Function.update_self] at hss'
      exact absurd hss' (hoff s hs h0)
    · rw [Function.update_of_ne h0, Function.update_of_ne h0'] at hss'
      exact hφi (hrδ ⟨hs, h0⟩) (hrδ ⟨hs', h0'⟩) hss'
  · intro s hs
    by_cases h0 : s = 0
    · subst h0
      rw [Function.update_self]
      exact hwY
    · rw [Function.update_of_ne h0]
      exact (hφY s (hrδ ⟨hs, h0⟩)).1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
