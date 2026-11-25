-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsRegularPointOf_exists_ball_chart_9fbbc9253110
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:00.470349+00:00
-- url     : https://prove2.me/submissions/d175e3d4-958e-4e6d-b5b5-65c553c64b11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusIdentity

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
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace IsRegularPointOf
theorem _root_.solution {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {z : σ → ℂ}
    (hz : IsRegularPointOf Y z) {W : Set (σ → ℂ)} (hW : W ∈ 𝓝 z) :
    ∃ (d : ℕ) (V : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧ IsOpen B ∧ IsPreconnected B ∧ AnalyticOnNhd ℂ g B ∧
        Y ∩ V = g '' B := by
  obtain ⟨hzY, d, A, O, V, g, hO, hV, hzV, hg, hAg, hYV⟩ := hz
  have hzO : z ∈ g '' O := by rw [← hYV]; exact ⟨hzY, hzV⟩
  obtain ⟨y₀, hy₀O, rfl⟩ := hzO
  have hN : interior W ∩ V ∈ 𝓝 (g y₀) := inter_mem (interior_mem_nhds.2 hW) (hV.mem_nhds hzV)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (hO.mem_nhds hy₀O) ((hg y₀ hy₀O).continuousAt.preimage_mem_nhds hN))
  refine ⟨d, V ∩ interior W ∩ A ⁻¹' Metric.ball y₀ r, Metric.ball y₀ r, g,
    (hV.inter isOpen_interior).inter (Metric.isOpen_ball.preimage A.continuous),
    ⟨⟨hzV, mem_interior_iff_mem_nhds.2 hW⟩, ?_⟩, fun x hx => interior_subset hx.1.2,
    Metric.isOpen_ball, (convex_ball y₀ r).isPreconnected, fun y hy => hg y (hball hy).1, ?_⟩
  · show A (g y₀) ∈ Metric.ball y₀ r
    rw [hAg y₀ hy₀O]
    exact Metric.mem_ball_self hr
  · ext x
    constructor
    · rintro ⟨hxY, ⟨hxV, -⟩, hxB⟩
      have hx : x ∈ g '' O := by rw [← hYV]; exact ⟨hxY, hxV⟩
      obtain ⟨y, hyO, rfl⟩ := hx
      have hyB : A (g y) ∈ Metric.ball y₀ r := hxB
      rw [hAg y hyO] at hyB
      exact ⟨y, hyB, rfl⟩
    · rintro ⟨y, hyB, rfl⟩
      have hyO : y ∈ O := (hball hyB).1
      have hyN : g y ∈ interior W ∩ V := (hball hyB).2
      have hgy : g y ∈ Y ∩ V := by rw [hYV]; exact ⟨y, hyO, rfl⟩
      refine ⟨hgy.1, ⟨hyN.2, hyN.1⟩, ?_⟩
      show A (g y) ∈ Metric.ball y₀ r
      rw [hAg y hyO]
      exact hyB
end IsRegularPointOf
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
