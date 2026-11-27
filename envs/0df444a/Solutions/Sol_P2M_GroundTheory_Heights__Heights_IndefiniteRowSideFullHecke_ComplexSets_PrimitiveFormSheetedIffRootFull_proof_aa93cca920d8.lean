-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedIffRootFull_proof_aa93cca920d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:59:18.46187+00:00
-- url     : https://prove2.me/submissions/b3437eca-a86a-437f-b3cc-add1f0947334

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedIffRootFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormSheetedIffRootFull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_simpleRoot_isolated_a6f4f915c882

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
namespace PrimitiveFormSheetedIffRootFull
theorem _root_.solution : PrimitiveFormSheetedIffRootFull.Statement := by
  intro σ _ X w d A ℓ N a δ q ha hδ hq hP hsep hQ

  obtain ⟨UA, hUA, hUAo, hwUA⟩ := eventually_nhds_iff.1
    ((eventually_all.2 fun j => (ha j).eventually_analyticAt).and
      (hδ.eventually_analyticAt.and
        ((eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyticAt).and hsep)))

  obtain ⟨UX, hUX, hUXo, hwUX⟩ := eventually_nhds_iff.1 (hP.and (eventually_all.2 hQ))
  set S : Set (σ → ℂ) := UX ∩ A ⁻¹' UA with hSdef
  have hSo : IsOpen S := hUXo.inter (hUAo.preimage A.continuous)
  set D : Set (Fin d → ℂ) := UA ∩ δ ⁻¹' {0}ᶜ with hDdef
  have hDo : IsOpen D := ContinuousOn.isOpen_inter_preimage
    (fun y hy => (hUA y hy).2.1.continuousAt.continuousWithinAt) hUAo isOpen_compl_singleton

  have hrep : ∀ x ∈ X, x ∈ S → δ (A x) ≠ 0 →
      (fun i => (∑ j, q i j (A x) * ℓ x ^ (j : ℕ)) / δ (A x)) = x := by
    intro x hxX hxS hδx
    funext i
    rw [← (hUX x hxS.1).2 i hxX, mul_div_cancel_left₀ _ hδx]
  filter_upwards [hSo.mem_nhds ⟨hwUX, hwUA⟩] with z hzS hzX hδz W hWo hzW
  have hzD : A z ∈ D := ⟨hzS.2, hδz⟩
  constructor
  · rintro ⟨O, V, g, hOo, hVo, hzV, hg, hAg, hXV⟩
    have hzg : z ∈ g '' O := by rw [← hXV]; exact ⟨hzX, hzV⟩
    obtain ⟨t₀, ht₀, hgt₀⟩ := hzg
    have hAz : A z = t₀ := by rw [← hgt₀, hAg t₀ ht₀]
    subst hAz
    have hO'o : IsOpen ((O ∩ g ⁻¹' (S ∩ W)) ∩ D) :=
      (hg.continuousOn.isOpen_inter_preimage hOo (hSo.inter hWo)).inter hDo
    refine ⟨(O ∩ g ⁻¹' (S ∩ W)) ∩ D, fun s => ℓ (g s), hO'o,
      ⟨⟨ht₀, by rw [Set.mem_preimage, hgt₀]; exact ⟨hzS, hzW⟩⟩, hzD⟩,
      fun s hs => (ℓ.analyticAt (g s)).comp (hg s hs.1.1), by simp only [hgt₀], fun s hs => ?_⟩
    have hgXV : g s ∈ X ∩ V := by rw [hXV]; exact Set.mem_image_of_mem g hs.1.1
    have hgs : (fun i => (∑ j, q i j s * ℓ (g s) ^ (j : ℕ)) / δ s) = g s := by
      have e := hrep (g s) hgXV.1 hs.1.2.1 (by rw [hAg s hs.1.1]; exact hs.2.2)
      rwa [hAg s hs.1.1] at e
    beta_reduce
    rw [hgs]
    exact ⟨⟨hgXV.1, hs.1.2.2⟩, hAg s hs.1.1, rfl⟩
  · rintro ⟨O, r, hOo, hzO, hr, hrz, hfull⟩
    set H : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hHdef
    have hfull' : ∀ s ∈ O, H s ∈ X ∩ W ∧ A (H s) = s ∧ ℓ (H s) = r s := hfull
    have hH : AnalyticOnNhd ℂ H (O ∩ D) := by
      intro s hs
      refine AnalyticAt.pi fun i => ?_
      exact (Finset.analyticAt_fun_sum _ fun j _ =>
        ((hUA s hs.2.1).2.2.1 i j).mul ((hr s hs.1).pow _)).div (hUA s hs.2.1).2.1 hs.2.2
    have hHz : H (A z) = z := by
      have e := hrep z hzX hzS hδz
      rw [← hrz] at e
      exact e
    obtain ⟨ε, hε, hiso⟩ := monic_simpleRoot_isolated a (A z) (ℓ z)
      (fun j => ((hUA (A z) hzS.2).1 j).continuousAt) ((hUA (A z) hzS.2).2.2.2 hδz) ((hUX z hzS.1).1 hzX)
    set B : Set (σ → ℂ) := S ∩ ℓ ⁻¹' Metric.ball (ℓ z) ε ∩ A ⁻¹' Metric.ball (A z) ε with hBdef
    have hBo : IsOpen B :=
      (hSo.inter (Metric.isOpen_ball.preimage ℓ.continuous)).inter (Metric.isOpen_ball.preimage A.continuous)
    have hzB : z ∈ B := ⟨⟨hzS, Metric.mem_ball_self hε⟩, Metric.mem_ball_self hε⟩
    have hO₁o : IsOpen ((O ∩ D) ∩ H ⁻¹' B) := hH.continuousOn.isOpen_inter_preimage (hOo.inter hDo) hBo
    have hzO₁ : A z ∈ (O ∩ D) ∩ H ⁻¹' B := ⟨⟨hzO, hzD⟩, by rw [Set.mem_preimage, hHz]; exact hzB⟩
    refine ⟨(O ∩ D) ∩ H ⁻¹' B, B ∩ A ⁻¹' ((O ∩ D) ∩ H ⁻¹' B), H, hO₁o,
      hBo.inter (hO₁o.preimage A.continuous), ⟨hzB, hzO₁⟩, fun s hs => hH s hs.1,
      fun s hs => (hfull' s hs.1.1).2.1, ?_⟩
    ext x
    constructor
    · rintro ⟨hxX, hxB, hxO⟩
      refine ⟨A x, hxO, ?_⟩
      have hs := hfull' (A x) hxO.1.1
      have hHB : H (A x) ∈ B := hxO.2

      have hroot : r (A x) ^ N + ∑ j, a j (A x) * r (A x) ^ (j : ℕ) = 0 := by
        have e := (hUX _ hHB.1.1.1).1 hs.1.1
        rwa [hs.2.1, hs.2.2] at e
      have hℓx : ℓ x = r (A x) := hiso (A x) hxB.2 (ℓ x) (r (A x)) hxB.1.2
        (by rw [← hs.2.2]; exact hHB.1.2) ((hUX x hxB.1.1.1).1 hxX) hroot
      have e := hrep x hxX hxB.1.1 hxO.1.2.2
      rw [hℓx] at e
      exact e
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(hfull' s hs.1.1).1.1, hs.2, by rw [Set.mem_preimage, (hfull' s hs.1.1).2.1]; exact hs⟩
end PrimitiveFormSheetedIffRootFull
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
