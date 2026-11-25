-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_locally_bounded_4ce462d07ee9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:19.874802+00:00
-- url     : https://prove2.me/submissions/c3df5131-a5a4-4bf1-88c0-76caa4094016

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperSheetedFibreEsymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_eq_51e9cd34a6ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_norm_esymm_map_le_3b7e6e724f88

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
open Topology Filter Set Complex
open scoped Real
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
theorem _root_.solution (hcount : UnbranchedProperCountConstant.Statement) {σ : Type} [Fintype σ]
    {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ) (hD : IsOpen D)
    (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) (hδ : AnalyticOnNhd ℂ δ D)
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {τ : Fin d → ℂ} (hτ : τ ∈ D) :
    ∃ N ∈ 𝓝 τ, Bornology.IsBounded (fibreEsymm Y A l j '' (N ∩ D ∩ {t | δ t ≠ 0})) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD τ hτ
  set B := Metric.ball τ (ε / 2)
  have hKD : Metric.closedBall τ (ε / 2) ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBD : B ⊆ D := Metric.ball_subset_closedBall.trans hKD

  obtain ⟨n, hn⟩ := hcount σ (Y ∩ A ⁻¹' B) d A B δ Metric.isOpen_ball (convex_ball τ _).isPreconnected
    (fun x hx => hx.2) (fun K hK hKc => by
      convert hprop K (hK.trans hBD) hKc using 1
      ext x; exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hK h.2⟩, h.2⟩⟩) (hδ.mono hBD) (by
      intro x hx hδx
      obtain ⟨O, V, g, hO, hV, hxV, hg, hsec, hYV⟩ := hchart x hx.1 hδx
      refine ⟨O ∩ B, V, g, hO.inter Metric.isOpen_ball, hV, hxV, hg.continuousOn.mono inter_subset_left,
        fun y hy => hsec y hy.1, ?_⟩
      ext z
      constructor
      · rintro ⟨⟨hzY, hzB⟩, hzV⟩
        obtain ⟨w, hw, rfl⟩ : z ∈ g '' O := hYV ▸ ⟨hzY, hzV⟩
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        have : A (g w) ∈ B := hzB
        rwa [hsec w hw] at this
      · rintro ⟨w, ⟨hw, hwB⟩, rfl⟩
        have hm : g w ∈ Y ∩ V := hYV ▸ mem_image_of_mem g hw
        refine ⟨⟨hm.1, ?_⟩, hm.2⟩
        show A (g w) ∈ B
        rwa [hsec w hw])

  obtain ⟨C, hC⟩ := (hprop _ hKD (isCompact_closedBall τ _)).exists_bound_of_continuousOn
    l.continuous.continuousOn
  refine ⟨B, Metric.ball_mem_nhds τ (half_pos hε), (Metric.isBounded_iff_subset_closedBall 0).2
    ⟨(n.choose j : ℝ) * C ^ j, ?_⟩⟩
  rintro _ ⟨t, ⟨⟨htB, -⟩, htδ⟩, rfl⟩
  have hfib : {x | x ∈ Y ∩ A ⁻¹' B ∧ A x = t} = {x | x ∈ Y ∧ A x = t} := by
    ext x; exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, show A x ∈ B from h.2 ▸ htB⟩, h.2⟩⟩
  have hcard := hn t htB htδ
  rw [hfib] at hcard
  have hfin : {x | x ∈ Y ∧ A x = t}.Finite := Set.finite_of_encard_eq_coe hcard
  rw [hfin.encard_eq_coe_toFinset_card, Nat.cast_inj] at hcard
  rw [Metric.mem_closedBall, dist_zero_right, fibreEsymm_eq hfin.toFinset hfin.coe_toFinset, ← hcard]
  refine norm_esymm_map_le _ _ _ fun x hx => hC x ?_
  rw [Set.Finite.mem_toFinset] at hx
  exact ⟨hx.1, hx.2 ▸ Metric.ball_subset_closedBall htB⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
