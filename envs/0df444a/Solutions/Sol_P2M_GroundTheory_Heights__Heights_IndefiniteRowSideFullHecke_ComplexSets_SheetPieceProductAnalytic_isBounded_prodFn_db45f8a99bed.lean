-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_isBounded_prodFn_db45f8a99bed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:48.372404+00:00
-- url     : https://prove2.me/submissions/199d4ec0-a5ed-4669-858f-7e39fb2e9d71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceProductAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedFibreSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetPieceProductAnalytic

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
open Topology Metric Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
theorem _root_.solution {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    (U : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) :
    ∃ Nb ∈ 𝓝 p₀, Bornology.IsBounded
      (prodFn X B U A ℓ '' (Nb ∩ tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0})) := by
  obtain ⟨-, -, hD, -, -, hprop, -, -, -, hcard, -, -⟩ := hP
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hD _ hp₀
  set y₀ := tailL d p₀ with hy₀def
  have hK : IsCompact {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
    hprop _ ((closedBall_subset_ball (half_lt_self hρ)).trans hρD) (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hK.image ℓ.continuous).isBounded
  set C : ℝ := max 1 (‖p₀ 0‖ + 1 + M) with hCdef
  refine ⟨tailL d ⁻¹' ball y₀ (ρ / 2) ∩ {p | ‖p 0‖ < ‖p₀ 0‖ + 1}, ?_, ?_⟩
  · refine Filter.inter_mem ((tailL d).continuous.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (mem_ball_self (half_pos hρ)))) ?_
    exact (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const).mem_nhds (by simp)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C ^ N, ?_⟩
  rintro _ ⟨p, ⟨⟨⟨hpb, hpn⟩, hpD⟩, hpδ⟩, rfl⟩
  have hpn' : ‖p 0‖ < ‖p₀ 0‖ + 1 := hpn
  have hsub : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} ⊆ {x | x ∈ X ∩ B ∧ A x = tailL d p} :=
    fun x hx => ⟨hx.1, hx.2.2⟩
  have hfin : {x | x ∈ X ∩ B ∧ A x = tailL d p}.encard = N := hcard _ hpD hpδ
  have hsfin : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}.Finite :=
    (Set.finite_of_encard_eq_coe hfin).subset hsub
  have hcardle : hsfin.toFinset.card ≤ N := by
    have h1 := Set.encard_le_encard hsub
    rw [hfin, ← hsfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at h1
    exact_mod_cast h1
  have hbd : ∀ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ ≤ C := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have hxK : x ∈ {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
      ⟨hx.1, by rw [hx.2.2]; exact ball_subset_closedBall hpb⟩
    have hMx := hM _ ⟨x, hxK, rfl⟩
    calc ‖p 0 - ℓ x‖ ≤ ‖p 0‖ + ‖ℓ x‖ := norm_sub_le _ _
      _ ≤ ‖p₀ 0‖ + 1 + M := by linarith
      _ ≤ C := le_max_right _ _
  unfold prodFn
  rw [finprod_mem_eq_finite_toFinset_prod _ hsfin]
  calc ‖∏ x ∈ hsfin.toFinset, (p 0 - ℓ x)‖ ≤ ∏ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _x ∈ hsfin.toFinset, C := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hbd
    _ = C ^ hsfin.toFinset.card := Finset.prod_const C
    _ ≤ C ^ N := pow_le_pow_right₀ (le_max_left _ _) hcardle
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
