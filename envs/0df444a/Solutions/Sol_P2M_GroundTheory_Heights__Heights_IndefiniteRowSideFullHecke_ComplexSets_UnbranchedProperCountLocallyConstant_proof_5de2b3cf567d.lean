-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_UnbranchedProperCountLocallyConstant_proof_5de2b3cf567d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:45.446329+00:00
-- url     : https://prove2.me/submissions/4f473808-c647-4fae-a0d3-fb2554e225bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountLocallyConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnbranchedProperCountLocallyConstant

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
namespace UnbranchedProperCountLocallyConstant
theorem _root_.solution : UnbranchedProperCountLocallyConstant.Statement := by
  intro σ _ Y d A D δ hD _ hprop hchart y hyD hδy
  choose! O V g hO hV hxV hg hsec hYV using hchart

  have key : ∀ x ∈ Y, δ (A x) ≠ 0 → ∀ z ∈ Y, z ∈ V x → A z ∈ O x ∧ g x (A z) = z := by
    intro x hx hδ z hz hzV
    obtain ⟨w, hw, rfl⟩ : z ∈ g x '' O x := hYV x hx hδ ▸ ⟨hz, hzV⟩
    rw [hsec x hx hδ w hw]; exact ⟨hw, rfl⟩
  set F := {x | x ∈ Y ∧ A x = y} with hFdef
  have hFδ : ∀ x ∈ F, δ (A x) ≠ 0 := fun x hx => hx.2 ▸ hδy
  have hyO : ∀ x ∈ F, y ∈ O x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).1
  have hgy : ∀ x ∈ F, g x y = x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).2

  have hFc : IsCompact F := by
    simpa [hFdef] using hprop {y} (singleton_subset_iff.2 hyD) isCompact_singleton
  have hFfin : F.Finite := by
    obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover V
      (fun x hx => (hV x hx.1 (hFδ x hx)).mem_nhds (hxV x hx.1 (hFδ x hx)))
    refine t.finite_toSet.subset fun z hz => ?_
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov hz)
    have hx := htF x hxt
    have := (key x hx.1 (hFδ x hx) z hz.1 hzx).2
    rw [hz.2, hgy x hx] at this
    exact this ▸ hxt
  refine ⟨hFfin, ?_⟩

  have hev1 : ∀ᶠ y' in 𝓝 y, ∀ x ∈ F, y' ∈ O x :=
    (eventually_all_finite hFfin).2 fun x hx => (hO x hx.1 (hFδ x hx)).mem_nhds (hyO x hx)

  have hev2 : ∀ᶠ y' in 𝓝 y, ∀ p ∈ F ×ˢ F, p.1 ≠ p.2 → g p.1 y' ≠ g p.2 y' := by
    refine (eventually_all_finite (hFfin.prod hFfin)).2 fun p hp => ?_
    by_cases hne : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hne h
    have c1 := ((hg p.1 hp.1.1 (hFδ _ hp.1)).continuousAt ((hO _ hp.1.1 (hFδ _ hp.1)).mem_nhds (hyO _ hp.1)))
    have c2 := ((hg p.2 hp.2.1 (hFδ _ hp.2)).continuousAt ((hO _ hp.2.1 (hFδ _ hp.2)).mem_nhds (hyO _ hp.2)))
    have hne' : g p.1 y ≠ g p.2 y := by rwa [hgy _ hp.1, hgy _ hp.2]
    exact ((c1.tendsto.prodMk_nhds c2.tendsto).eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds hne')).mono fun _ h _ => h

  have hev3 : ∀ᶠ y' in 𝓝 y, ∀ z ∈ Y, A z = y' → ∃ x ∈ F, z ∈ V x := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD y hyD
    set K := Metric.closedBall y (ε / 2)
    have hKD : K ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
    set W := ⋃ x ∈ F, V x
    have hW : IsOpen W := isOpen_biUnion fun x hx => hV x hx.1 (hFδ x hx)
    have hC : IsCompact ({z | z ∈ Y ∧ A z ∈ K} \ W) :=
      (hprop K hKD (isCompact_closedBall y _)).diff hW
    have hyn : y ∉ A '' ({z | z ∈ Y ∧ A z ∈ K} \ W) := by
      rintro ⟨z, ⟨⟨hzY, -⟩, hzW⟩, hzy⟩
      exact hzW (mem_iUnion₂.2 ⟨z, ⟨hzY, hzy⟩, hxV z hzY (hzy ▸ hδy)⟩)
    filter_upwards [Metric.closedBall_mem_nhds y (half_pos hε),
      (hC.image A.continuous).isClosed.isOpen_compl.mem_nhds hyn] with y' hy'K hy'C z hzY hzy
    by_contra hno
    exact hy'C ⟨z, ⟨⟨hzY, hzy ▸ hy'K⟩, fun h => hno (by simpa [W] using h)⟩, hzy⟩
  filter_upwards [hev1, hev2, hev3] with y' h1 h2 h3
  have himg : {x | x ∈ Y ∧ A x = y'} = (fun x => g x y') '' F := by
    ext z
    constructor
    · rintro ⟨hzY, hzy⟩
      obtain ⟨x, hx, hzx⟩ := h3 z hzY hzy
      exact ⟨x, hx, by simpa [hzy] using (key x hx.1 (hFδ x hx) z hzY hzx).2⟩
    · rintro ⟨x, hx, rfl⟩
      have hm : g x y' ∈ Y ∩ V x := hYV x hx.1 (hFδ x hx) ▸ mem_image_of_mem _ (h1 x hx)
      exact ⟨hm.1, hsec x hx.1 (hFδ x hx) y' (h1 x hx)⟩
  rw [himg]
  refine InjOn.encard_image fun a ha b hb hab => ?_
  by_contra hne
  exact h2 (a, b) ⟨ha, hb⟩ hne hab
end UnbranchedProperCountLocallyConstant
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
