-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_local_filter_eq_81399f299053
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:28.175825+00:00
-- url     : https://prove2.me/submissions/6a263a7a-f88f-46b7-a47b-096e782e5cce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_fiberPoly_card_roots_f4bf3eaf143a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_mem_roots_fiberPoly_501f147fc65c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticRootBranch_proof_ddb790907339
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_proof_6f657cf29ce3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_proof_9f4f3171a0d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4


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
open Polynomial Filter Topology Classical
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
theorem _root_.solution {d N : ℕ} {a : Fin N → (Fin d → ℂ) → ℂ} {Q : (Fin d → ℂ) → ℂ → Prop}
    {t₀ : Fin d → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) t₀) (hsep : (fiberPoly a t₀).Separable)
    (hbr : ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧ (Q s (r s) ↔ Q t₀ τ₀)) :
    ∃ ρ : ℂ → (Fin d → ℂ) → ℂ, (∀ τ, DifferentiableAt ℂ (ρ τ) t₀) ∧
      ∀ᶠ s in 𝓝 t₀, (fiberPoly a s).roots.filter (Q s) =
        ((fiberPoly a t₀).roots.filter (Q t₀)).map fun τ => ρ τ s := by
  set R₀ := (fiberPoly a t₀).roots with hR₀
  have hA : ∀ τ : ℂ, ∃ (O : Set (Fin d → ℂ)) (ρ : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧
      DifferentiableAt ℂ ρ t₀ ∧ (τ ∈ R₀ → ρ t₀ = τ ∧ ∀ s ∈ O, ρ s ∈ (fiberPoly a s).roots) := by
    intro τ
    by_cases hτ : τ ∈ R₀
    · obtain ⟨O, ρ, hO, ht, hρ, hρ0, hρr⟩ :=
        AnalyticRootBranch.proof d N a t₀ τ ha hsep ((mem_roots_fiberPoly a t₀ τ).1 hτ)
      exact ⟨O, ρ, hO, ht, (hρ t₀ ht).differentiableAt, fun _ =>
        ⟨hρ0, fun s hs => (mem_roots_fiberPoly a s _).2 (hρr s hs)⟩⟩
    · exact ⟨Set.univ, fun _ => τ, isOpen_univ, trivial, differentiableAt_const _, fun h => absurd h hτ⟩
  choose O ρ hO ht₀ hρd hρ using hA
  have hC : ∀ τ : ℂ, ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧
      (τ ∈ R₀ → ContinuousAt r t₀ ∧ r t₀ = τ ∧
        ∀ s ∈ O, r s ∈ (fiberPoly a s).roots ∧ (Q s (r s) ↔ Q t₀ τ)) := by
    intro τ
    by_cases hτ : τ ∈ R₀
    · obtain ⟨O, r, hO, ht, hr, hr0, hrr⟩ := hbr τ ((mem_roots_fiberPoly a t₀ τ).1 hτ)
      exact ⟨O, r, hO, ht, fun _ => ⟨hr.continuousAt (hO.mem_nhds ht), hr0, fun s hs =>
        ⟨(mem_roots_fiberPoly a s _).2 (hrr s hs).1, (hrr s hs).2⟩⟩⟩
    · exact ⟨Set.univ, fun _ => τ, isOpen_univ, trivial, fun h => absurd h hτ⟩
  choose O' r hO' ht₀' hr using hC
  have ev1 : ∀ᶠ s in 𝓝 t₀, ∀ τ ∈ R₀.toFinset, s ∈ O τ ∧ s ∈ O' τ :=
    (eventually_all_finset _).2 fun τ _ =>
      Filter.Eventually.and ((hO τ).mem_nhds (ht₀ τ)) ((hO' τ).mem_nhds (ht₀' τ))
  have ev2 : ∀ᶠ s in 𝓝 t₀, ∀ σ ∈ R₀.toFinset, ∀ τ ∈ R₀.toFinset,
      σ ≠ τ → ρ σ s ≠ ρ τ s ∧ r τ s ≠ ρ σ s := by
    refine (eventually_all_finset _).2 fun σ hσ => (eventually_all_finset _).2 fun τ hτ => ?_
    rw [Multiset.mem_toFinset] at hσ hτ
    by_cases hστ : σ = τ
    · exact Eventually.of_forall fun _ h => absurd hστ h
    have c1 : ContinuousAt (fun s => ρ σ s - ρ τ s) t₀ := (hρd σ).continuousAt.sub (hρd τ).continuousAt
    have c2 : ContinuousAt (fun s => r τ s - ρ σ s) t₀ := (hr τ hτ).1.sub (hρd σ).continuousAt
    have e1 : ρ σ t₀ - ρ τ t₀ ≠ 0 := by
      rw [(hρ σ hσ).1, (hρ τ hτ).1]; exact sub_ne_zero.2 hστ
    have e2 : r τ t₀ - ρ σ t₀ ≠ 0 := by
      rw [(hr τ hτ).2.1, (hρ σ hσ).1]; exact sub_ne_zero.2 (Ne.symm hστ)
    filter_upwards [c1.eventually_ne e1, c2.eventually_ne e2] with s h1 h2 _
    exact ⟨sub_ne_zero.1 h1, sub_ne_zero.1 h2⟩
  refine ⟨ρ, hρd, ?_⟩
  filter_upwards [ev1, ev2] with s h1 h2
  have h1' : ∀ τ ∈ R₀, s ∈ O τ ∧ s ∈ O' τ := fun τ hτ => h1 τ (Multiset.mem_toFinset.2 hτ)
  have h2' : ∀ σ ∈ R₀, ∀ τ ∈ R₀, σ ≠ τ → ρ σ s ≠ ρ τ s ∧ r τ s ≠ ρ σ s := fun σ hσ τ hτ =>
    h2 σ (Multiset.mem_toFinset.2 hσ) τ (Multiset.mem_toFinset.2 hτ)
  have hnd : R₀.Nodup := nodup_roots hsep
  have hMnd : (R₀.map fun τ => ρ τ s).Nodup := hnd.map_on fun σ hσ τ hτ h => by
    by_contra hne
    exact (h2' σ hσ τ hτ hne).1 h
  have hMsub : (R₀.map fun τ => ρ τ s) ⊆ (fiberPoly a s).roots := by
    intro x hx
    obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 hx
    exact (hρ τ hτ).2 s (h1' τ hτ).1
  have hMeq : (R₀.map fun τ => ρ τ s) = (fiberPoly a s).roots := by
    refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hMnd).2 hMsub) ?_
    rw [Multiset.card_map, hR₀, fiberPoly_card_roots, fiberPoly_card_roots]
  rw [← hMeq, Multiset.filter_map]
  refine congrArg (Multiset.map _) (Multiset.filter_congr fun τ hτ => ?_)
  have hrs : r τ s ∈ (fiberPoly a s).roots := ((hr τ hτ).2.2 s (h1' τ hτ).2).1
  rw [← hMeq] at hrs
  obtain ⟨σ, hσ, hσe⟩ := Multiset.mem_map.1 hrs
  have hστ : σ = τ := by
    by_contra hne
    exact (h2' σ hσ τ hτ hne).2 hσe.symm
  rw [hστ] at hσe
  show Q s (ρ τ s) ↔ Q t₀ τ
  rw [hσe]
  exact ((hr τ hτ).2.2 s (h1' τ hτ).2).2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
