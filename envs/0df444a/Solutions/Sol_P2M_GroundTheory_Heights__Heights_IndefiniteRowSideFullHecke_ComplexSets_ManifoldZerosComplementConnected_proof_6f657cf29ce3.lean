-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_proof_6f657cf29ce3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:10.78201+00:00
-- url     : https://prove2.me/submissions/c15c3a3e-e805-4bb9-ba2b-f3ca61205ffd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_of_local_112b6a22accd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_convex_inter_ne_zero_5a3afb509677

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
open Topology Filter Set
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ManifoldZerosComplementConnected
theorem _root_.solution : ManifoldZerosComplementConnected.Statement := by
  intro σ _ R h hR hreg hh ⟨x₀, hx₀R, hx₀⟩

  have chart : ∀ x ∈ R, ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (W : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen B ∧ Convex ℝ B ∧ IsOpen W ∧ x ∈ W ∧ AnalyticOnNhd ℂ g B ∧ R ∩ W = g '' B := by
    intro x hx
    obtain ⟨-, d, A, O, V, g, hO, hV, hxV, hg, hAg, hRV⟩ := hreg x hx
    have hxO : A x ∈ O := by
      obtain ⟨y, hy, hgy⟩ : x ∈ g '' O := hRV ▸ ⟨hx, hxV⟩
      rw [← hgy, hAg y hy]
      exact hy
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO (A x) hxO
    refine ⟨d, Metric.ball (A x) ε, V ∩ A ⁻¹' Metric.ball (A x) ε, g, Metric.isOpen_ball,
      convex_ball _ _, hV.inter (Metric.isOpen_ball.preimage A.continuous),
      ⟨hxV, Metric.mem_ball_self hε⟩, hg.mono hεO, ?_⟩
    ext z
    constructor
    · rintro ⟨hzR, hzV, hzB⟩
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' O := hRV ▸ ⟨hzR, hzV⟩
      have hAy : A (g y) ∈ Metric.ball (A x) ε := hzB
      rw [hAg y hy] at hAy
      exact ⟨y, hAy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hgy : g y ∈ R ∩ V := by rw [hRV]; exact ⟨y, hεO hy, rfl⟩
      refine ⟨hgy.1, hgy.2, ?_⟩
      show A (g y) ∈ Metric.ball (A x) ε
      rw [hAg y (hεO hy)]
      exact hy
  have chartR : ∀ {d : ℕ} {B : Set (Fin d → ℂ)} {W : Set (σ → ℂ)} {g : (Fin d → ℂ) → σ → ℂ},
      R ∩ W = g '' B → ∀ y ∈ B, g y ∈ R := by
    intro d B W g hRW y hy
    have : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
    exact this.1

  let T : Set (σ → ℂ) := {x | ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0}
  have hTo : IsOpen T := isOpen_setOfPred_eventually_nhds
  let T₂ : Set (σ → ℂ) := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ z ∈ W ∩ R, z ∉ T}
  have hT₂o : IsOpen T₂ := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWT⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWT⟩, hW, hxW⟩
  have hcov : R ⊆ T ∪ T₂ := by
    intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    by_cases hzero : ∃ y ∈ B, ∀ᶠ y' in 𝓝 y, h (g y') = 0
    · obtain ⟨y, hy, hev⟩ := hzero
      have hEq := hhg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc.isPreconnected hy hev
      left
      show ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0
      filter_upwards [hWo.mem_nhds hxW] with z hzW hzR
      obtain ⟨y', hy', rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      exact hEq hy'
    · right
      refine ⟨W, hWo, hxW, ?_⟩
      rintro z ⟨hzW, hzR⟩ hzT
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      have hzT' : ∀ᶠ w in 𝓝 (g y), w ∈ R → h w = 0 := hzT
      refine hzero ⟨y, hy, ?_⟩
      filter_upwards [(hg y hy).continuousAt.tendsto.eventually hzT', hBo.mem_nhds hy] with y' h1 h2
      exact h1 (chartR hRW y' h2)

  have hTR : ∀ x ∈ R, ¬ ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0 := by
    intro x hx hxT
    have hx₀T₂ : x₀ ∈ T₂ := by
      rcases hcov hx₀R with h1 | h1
      · exact absurd ((show ∀ᶠ z in 𝓝 x₀, z ∈ R → h z = 0 from h1).self_of_nhds hx₀R) hx₀
      · exact h1
    obtain ⟨y, hyR, hyT, W, -, hyW, hWT⟩ := hR T T₂ hTo hT₂o hcov ⟨x, hx, hxT⟩ ⟨x₀, hx₀R, hx₀T₂⟩
    exact hWT y ⟨hyW, hyR⟩ hyT
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hR sdiff_subset ?_ ?_
  · intro x hx
    rw [mem_closure_iff_frequently]
    exact (Filter.not_eventually.mp (hTR x hx)).mono fun z hz => Classical.not_imp.mp hz
  · intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    refine ⟨W, hWo, hxW, ?_⟩
    have heq : W ∩ (R \ {z | h z = 0}) = g '' (B ∩ {y | h (g y) ≠ 0}) := by
      ext z
      constructor
      · rintro ⟨hzW, hzR, hz⟩
        obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
        exact ⟨y, ⟨hy, hz⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
        have hgy : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
        exact ⟨hgy.2, hgy.1, hy'⟩
    rw [heq]
    exact (ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero hBo hBc hhg).image g
      (hg.continuousOn.mono inter_subset_left)
end ManifoldZerosComplementConnected
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
