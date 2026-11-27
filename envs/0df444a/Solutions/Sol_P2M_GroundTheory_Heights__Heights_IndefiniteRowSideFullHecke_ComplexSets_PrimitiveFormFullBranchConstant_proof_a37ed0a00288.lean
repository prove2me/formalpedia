-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormFullBranchConstant_proof_a37ed0a00288
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:50.919856+00:00
-- url     : https://prove2.me/submissions/d90ad03d-9d06-48da-a677-a491eff33080

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormFullBranchConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormFullBranchConstant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_root_branch_eventuallyEq_94398728a4f6

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
open Filter Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PrimitiveFormFullBranchConstant
theorem _root_.solution : PrimitiveFormFullBranchConstant.Statement := by
  intro σ _ X W N' k f d A ℓ N a δ q B O r hW hN' hWN' hf hXN' hXW hP hB ha hδ hq hO hOc hOB hδO hsep hr hrO
  set G : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hGdef
  set P : (Fin d → ℂ) → Prop := fun u => G u ∈ X ∩ W ∧ A (G u) = u ∧ ℓ (G u) = r u with hPdef
  have hG : AnalyticOnNhd ℂ G O := fun u hu => analyticAt_pi_iff.2 fun i =>
    (Finset.analyticAt_fun_sum _ fun j _ => (hq i j u (hOB hu)).mul ((hr u hu).pow _)).div
      (hδ u (hOB hu)) (hδO u hu)

  have hfull : ∀ s ∈ O, (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ ∀ᶠ u in 𝓝 s, P u) := by
    intro s hs
    constructor
    · rintro ⟨O', r', hO', hsO', hr', hrs, hw⟩
      have hroot' : ∀ᶠ u in 𝓝 s, r' u ^ N + ∑ j, a j u * r' u ^ (j : ℕ) = 0 := by
        filter_upwards [hO'.mem_nhds hsO'] with u hu
        obtain ⟨hX, hA, hℓ⟩ := hw u hu
        have h := hP _ hX
        rwa [hA, hℓ] at h
      have heq : r' =ᶠ[𝓝 s] r := monic_root_branch_eventuallyEq a s r' r
        (fun j => (ha j s (hOB hs)).continuousAt) (hr' s hsO').continuousAt (hr s hs).continuousAt hrs
        (hsep s hs) hroot' (Filter.mem_of_superset (hO.mem_nhds hs) hrO)
      filter_upwards [hO'.mem_nhds hsO', heq] with u hu hru
      have h := hw u hu
      simp only [hru] at h
      exact h
    · intro hev
      obtain ⟨U, hUs, hUo, hsU⟩ := mem_nhds_iff.1 hev
      exact ⟨U ∩ O, r, hUo.inter hO, ⟨hsU, hs⟩, hr.mono Set.inter_subset_right, rfl, fun u hu => hUs hu.1⟩

  set S : Set (Fin d → ℂ) := {s | ∀ᶠ u in 𝓝 s, P u} with hSdef
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hSc : closure S ∩ O ⊆ S := by
    rintro s ⟨hsc, hs⟩
    have hGs : ContinuousAt G s := (hG s hs).continuousAt
    have hGW : G s ∈ closure W := closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact hu.self_of_nhds.1.2)
      (mem_closure_image hGs hsc)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
      (Filter.inter_mem (hO.mem_nhds hs) (hGs.preimage_mem_nhds (hN'.mem_nhds (hWN' hGW))))

    set Φ : (Fin d → ℂ) → (Fin k → ℂ) × (Fin d → ℂ) × ℂ :=
      fun u => (fun i => f i (G u), A (G u) - u, ℓ (G u) - r u) with hΦdef
    have hΦ : AnalyticOnNhd ℂ Φ (Metric.ball s ε) := fun u hu => by
      have hu' := hball hu
      exact (analyticAt_pi_iff.2 fun i => (hf i _ hu'.2).comp (hG u hu'.1)).prod
        ((((A.analyticAt _).comp (hG u hu'.1)).sub analyticAt_id).prod
          (((ℓ.analyticAt _).comp (hG u hu'.1)).sub (hr u hu'.1)))
    obtain ⟨u₀, hu₀U, hu₀S⟩ := mem_closure_iff.1 hsc _ Metric.isOpen_ball (Metric.mem_ball_self hε)
    have hΦ0 : Set.EqOn Φ 0 (Metric.ball s ε) :=
      hΦ.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball s ε).isPreconnected hu₀U (by
        filter_upwards [hu₀S] with u hu
        obtain ⟨⟨hX, hWu⟩, hA, hℓ⟩ := hu
        have hXN : G u ∈ X ∩ N' := ⟨hX, hWN' (subset_closure hWu)⟩
        rw [hXN'] at hXN
        simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, hA, hℓ, sub_self, and_true]
        exact funext fun i => hXN.2 i)
    have hU : ∀ u ∈ Metric.ball s ε, G u ∈ X ∧ A (G u) = u ∧ ℓ (G u) = r u := by
      intro u hu
      have h := hΦ0 hu
      simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, sub_eq_zero] at h
      refine ⟨?_, h.2.1, h.2.2⟩
      have hXN : G u ∈ X ∩ N' := by rw [hXN']; exact ⟨(hball hu).2, fun i => congr_fun h.1 i⟩
      exact hXN.1
    obtain ⟨hXs, hAs, -⟩ := hU s (Metric.mem_ball_self hε)
    have hGsW : G s ∈ W := hXW _ ⟨hXs, hGW⟩ (by rw [hAs]; exact hOB hs)
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε),
      hGs.preimage_mem_nhds (hW.mem_nhds hGsW)] with u hu hu'
    obtain ⟨h1, h2, h3⟩ := hU u hu
    exact ⟨⟨h1, hu'⟩, h2, h3⟩

  have key : ∀ s ∈ O, ∀ s' ∈ O, PrimitiveFormRootFull X W A ℓ δ q s (r s) →
      PrimitiveFormRootFull X W A ℓ δ q s' (r s') := by
    intro s hs s' hs' h
    have hsub : O ⊆ S := hOc.subset_of_closure_inter_subset hSo ⟨s, hs, (hfull s hs).1 h⟩ hSc
    exact (hfull s' hs').2 (hsub hs')
  intro s hs s' hs'
  exact ⟨key s hs s' hs', key s' hs' s hs⟩
end PrimitiveFormFullBranchConstant
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
