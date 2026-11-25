-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_extended_factor_edafc28f6428
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:39.087746+00:00
-- url     : https://prove2.me/submissions/6d5e151f-0dda-4ac8-a05d-7dd28e52e2cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_rootFactor_monic_c06104680060
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_rootFactor_natDegree_3454157c1a46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_norm_coeff_rootFactor_le_e7c6d9ab8225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_differentiableAt_coeff_prod_974a041f6356
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_exists_ne_zero_of_open_c7e4de96daad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_local_filter_eq_81399f299053
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticRootBranch_proof_ddb790907339
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_convex_inter_ne_zero_5a3afb509677
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_proof_6f657cf29ce3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_analyticOnNhd_of_differentiableOn_c966cce3f6fd
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
theorem _root_.solution {d N : ℕ} {B : Set (Fin d → ℂ)} {a : Fin N → (Fin d → ℂ) → ℂ} {δ : (Fin d → ℂ) → ℂ}
    (Q : (Fin d → ℂ) → ℂ → Prop) (hBo : IsOpen B) (hBc : Convex ℝ B) (ha : ∀ j, AnalyticOnNhd ℂ (a j) B)
    (hδ : AnalyticOnNhd ℂ δ B) {t₁ : Fin d → ℂ} (ht₁B : t₁ ∈ B) (ht₁ : δ t₁ ≠ 0)
    (hsep : ∀ t ∈ B, δ t ≠ 0 → (fiberPoly a t).Separable)
    (hbr : ∀ t₀ ∈ B, δ t₀ ≠ 0 → ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧ (Q s (r s) ↔ Q t₀ τ₀)) :
    ∃ (m : ℕ) (F : ℕ → (Fin d → ℂ) → ℂ), (∀ k, AnalyticOnNhd ℂ (F k) B) ∧
      ∀ t ∈ B, δ t ≠ 0 →
        rootFactor (fiberPoly a t) (Q t) = X ^ m + ∑ k ∈ Finset.range m, C (F k t) * X ^ k := by
  have hdense := exists_ne_zero_of_open hBc hδ ht₁B ht₁
  have hB'c : IsPreconnected (B ∩ {t | δ t ≠ 0}) :=
    ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero hBo hBc hδ
  have hloc : ∀ t₀ ∈ B, δ t₀ ≠ 0 → ∃ ρ : ℂ → (Fin d → ℂ) → ℂ, (∀ τ, DifferentiableAt ℂ (ρ τ) t₀) ∧
      ∀ᶠ s in 𝓝 t₀, (fiberPoly a s).roots.filter (Q s) =
        ((fiberPoly a t₀).roots.filter (Q t₀)).map fun τ => ρ τ s :=
    fun t₀ h₀ hδ₀ => local_filter_eq (fun j => ha j t₀ h₀) (hsep t₀ h₀ hδ₀) (hbr t₀ h₀ hδ₀)
  have hcount : ∀ t ∈ B, δ t ≠ 0 → Multiset.card ((fiberPoly a t).roots.filter (Q t)) =
      Multiset.card ((fiberPoly a t₁).roots.filter (Q t₁)) := by
    intro t ht hδt
    refine hB'c.constant (f := fun t => Multiset.card ((fiberPoly a t).roots.filter (Q t))) ?_
      ⟨ht, hδt⟩ ⟨ht₁B, ht₁⟩
    rintro s ⟨hs, hδs⟩
    obtain ⟨ρ, -, hev⟩ := hloc s hs hδs
    refine (Filter.EventuallyEq.continuousAt
      (y := Multiset.card ((fiberPoly a s).roots.filter (Q s))) ?_).continuousWithinAt
    filter_upwards [hev] with u hu
    rw [hu, Multiset.card_map]
  have hdiff : ∀ k, DifferentiableOn ℂ (fun t => (rootFactor (fiberPoly a t) (Q t)).coeff k)
      (B ∩ {t | δ t ≠ 0}) := by
    rintro k t ⟨ht, hδt⟩
    obtain ⟨ρ, hρ, hev⟩ := hloc t ht hδt
    refine (DifferentiableAt.congr_of_eventuallyEq
      (differentiableAt_coeff_prod ((fiberPoly a t).roots.filter (Q t)) ρ t hρ k) ?_).differentiableWithinAt
    filter_upwards [hev] with s hs
    simp only [rootFactor, hs, Multiset.map_map, Function.comp_def]
  have hbdd : ∀ k, ∀ τ ∈ B, ∃ V ∈ 𝓝 τ, Bornology.IsBounded
      ((fun t => (rootFactor (fiberPoly a t) (Q t)).coeff k) '' (V ∩ B ∩ {t | δ t ≠ 0})) := by
    intro k τ₀ hτ₀
    refine ⟨{t | ∀ j, ‖a j t‖ < ‖a j τ₀‖ + 1}, Filter.eventually_all.2 fun j =>
      ((ha j τ₀ hτ₀).continuousAt.norm).eventually (gt_mem_nhds (lt_add_one _)), ?_⟩
    refine isBounded_iff_forall_norm_le.2 ⟨(1 + ∑ j, (‖a j τ₀‖ + 1)) ^ N * 2 ^ N, ?_⟩
    rintro _ ⟨t, ⟨⟨htV, -⟩, -⟩, rfl⟩
    refine (norm_coeff_rootFactor_le a t (Q t) k).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ N) (by positivity))
    gcongr with j
    exact (htV j).le
  have hext : ∀ k, ∃ Fk : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ Fk B ∧
      Set.EqOn Fk (fun t => (rootFactor (fiberPoly a t) (Q t)).coeff k) (B ∩ {t | δ t ≠ 0}) :=
    fun k => RiemannExtensionAnalytic.proof d B δ _ hBo hδ.differentiableOn hdense (hdiff k) (hbdd k)
  choose F hFd hFe using hext
  refine ⟨Multiset.card ((fiberPoly a t₁).roots.filter (Q t₁)), F,
    fun k => RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hBo (hFd k), ?_⟩
  intro t ht hδt
  have hdeg : (rootFactor (fiberPoly a t) (Q t)).natDegree =
      Multiset.card ((fiberPoly a t₁).roots.filter (Q t₁)) := by
    rw [rootFactor_natDegree, hcount t ht hδt]
  conv_lhs => rw [(rootFactor_monic (fiberPoly a t) (Q t)).as_sum, hdeg]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [hFe k ⟨ht, hδt⟩]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
