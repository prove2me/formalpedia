-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_differentiableAt_prodFn_c88dec3fd0bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:45.12163+00:00
-- url     : https://prove2.me/submissions/d64afa48-f0d0-46f3-b3f8-3685a3a28879

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
theorem _root_.solution (hsec : UnbranchedFibreSections.Statement)
    {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    {U V : Set (σ → ℂ)} (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V)
    (hdisj : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅)
    {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) (hδp₀ : δ (tailL d p₀) ≠ 0) :
    DifferentiableAt ℂ (prodFn X B U A ℓ) p₀ := by
  classical
  obtain ⟨r, g, hr, -, hrδ, hg, hfib⟩ := hsec σ X w B d A D δ N hP _ hp₀ hδp₀
  set y₀ := tailL d p₀ with hy₀def
  have hy₀ : y₀ ∈ ball y₀ r := mem_ball_self hr
  have hconst : ∀ i, ∀ y ∈ ball y₀ r, (g i y ∈ U ↔ g i y₀ ∈ U) := by
    intro i
    have hgc : ContinuousOn (g i) (ball y₀ r) := (hg i).continuousOn
    have hS : ∀ y ∈ ball y₀ r, g i y ∈ X ∩ B ∧ δ (A (g i y)) ≠ 0 := by
      intro y hy
      have hx : g i y ∈ {x | x ∈ X ∩ B ∧ A x = y} := by
        rw [(hfib y hy).2]
        exact ⟨i, rfl⟩
      exact ⟨hx.1, by rw [hx.2]; exact hrδ y hy⟩
    have hopU := hgc.isOpen_inter_preimage isOpen_ball hU
    have hopV := hgc.isOpen_inter_preimage isOpen_ball hV
    have hdj : Disjoint (ball y₀ r ∩ g i ⁻¹' U) (ball y₀ r ∩ g i ⁻¹' V) := by
      rw [Set.disjoint_left]
      rintro y ⟨hy, hyU⟩ ⟨-, hyV⟩
      have : g i y ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hS y hy, hyU, hyV⟩
      rw [hdisj] at this
      exact this
    have hcv : ball y₀ r ⊆ (ball y₀ r ∩ g i ⁻¹' U) ∪ (ball y₀ r ∩ g i ⁻¹' V) := by
      intro y hy
      rcases hcov (hS y hy) with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    have hc : IsPreconnected (ball y₀ r) := (convex_ball y₀ r).isPreconnected
    intro y hy
    constructor
    · intro hyU
      by_contra hy0U
      have hy0V : y₀ ∈ ball y₀ r ∩ g i ⁻¹' V := (hcv hy₀).resolve_left fun h => hy0U h.2
      have hsub := hc.subset_right_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy0V⟩
      exact Set.disjoint_left.1 hdj ⟨hy, hyU⟩ (hsub hy)
    · intro hy0U
      exact (hc.subset_left_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy₀, hy0U⟩ hy).2
  set I : Finset (Fin N) := Finset.univ.filter fun i => g i y₀ ∈ U with hIdef
  have hrep : ∀ p : Fin (d + 1) → ℂ, tailL d p ∈ ball y₀ r →
      prodFn X B U A ℓ p = ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    intro p hp
    have hset : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} =
        (fun i => g i (tailL d p)) '' (I : Set (Fin N)) := by
      ext x
      constructor
      · rintro ⟨hxB, hxU, hxA⟩
        have hx : x ∈ Set.range (fun i => g i (tailL d p)) := by
          rw [← (hfib _ hp).2]
          exact ⟨hxB, hxA⟩
        obtain ⟨i, rfl⟩ := hx
        exact ⟨i, by simpa [hIdef] using (hconst i _ hp).1 hxU, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hx : g i (tailL d p) ∈ {x | x ∈ X ∩ B ∧ A x = tailL d p} := by
          rw [(hfib _ hp).2]
          exact ⟨i, rfl⟩
        exact ⟨hx.1, (hconst i _ hp).2 (by simpa [hIdef] using hi), hx.2⟩
    unfold prodFn
    rw [hset, finprod_mem_image ((hfib _ hp).1.injOn), finprod_mem_coe_finset]
  have hev : prodFn X B U A ℓ =ᶠ[𝓝 p₀] fun p => ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    have hmem : tailL d ⁻¹' ball y₀ r ∈ 𝓝 p₀ :=
      (tailL d).continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hy₀)
    filter_upwards [hmem] with p hp using hrep p hp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hfac : ∀ i, DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0 - ℓ (g i (tailL d p))) p₀ := by
    intro i
    have h1 : DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0) p₀ := differentiableAt_apply 0 p₀
    have h2 : DifferentiableAt ℂ (fun p => ℓ (g i (tailL d p))) p₀ :=
      ℓ.differentiableAt.comp _ (((hg i) _ hy₀).differentiableAt.comp _ (tailL d).differentiableAt)
    exact h1.sub h2
  refine Finset.induction_on I ?_ ?_
  · simp
  · intro j s hj ih
    simp only [Finset.prod_insert hj]
    exact (hfac j).mul ih
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
