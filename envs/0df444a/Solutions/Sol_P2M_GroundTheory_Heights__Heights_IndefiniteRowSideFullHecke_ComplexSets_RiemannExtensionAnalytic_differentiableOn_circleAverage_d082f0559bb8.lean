-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_differentiableOn_circleAverage_d082f0559bb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:21.269564+00:00
-- url     : https://prove2.me/submissions/999047a1-cad0-41ca-b4a7-cbee0ce2d7ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_analyticOnNhd_of_differentiableOn_c966cce3f6fd

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
open Metric Filter Topology Set Complex MeasureTheory
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
theorem _root_.solution {k : ℕ} {O : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → ℂ}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) {τ₀ v : Fin k → ℂ} {ρ δ : ℝ} (hρ : 0 ≤ ρ)
    (hK : ∀ τ ∈ closedBall τ₀ δ, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ O) :
    DifferentiableOn ℂ (fun τ => ∫ θ in (0 : ℝ)..2 * π, f (τ + circleMap 0 ρ θ • v)) (ball τ₀ δ) := by
  have hcd : ContinuousOn (fderiv ℂ f) O :=
    ((analyticOnNhd_of_differentiableOn hO hf).contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hO le_rfl
  have hPc : Continuous fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v := by fun_prop
  have hKc : IsCompact ((fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v) '' (closedBall τ₀ δ ×ˢ sphere (0 : ℂ) ρ)) :=
    ((isCompact_closedBall τ₀ δ).prod (isCompact_sphere 0 ρ)).image hPc
  have hKO : (fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v) '' (closedBall τ₀ δ ×ˢ sphere (0 : ℂ) ρ) ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact hK p.1 hp.1 p.2 hp.2
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcd.mono hKO)
  have hmem : ∀ τ ∈ closedBall τ₀ δ, ∀ θ : ℝ, τ + circleMap 0 ρ θ • v ∈ O := fun τ hτ θ =>
    hK τ hτ _ (circleMap_mem_sphere 0 hρ θ)
  have hcont : ∀ τ ∈ closedBall τ₀ δ, Continuous fun θ : ℝ => f (τ + circleMap 0 ρ θ • v) :=
    fun τ hτ => hf.continuousOn.comp_continuous (by fun_prop) (hmem τ hτ)
  intro τ₁ hτ₁
  have hs : ball τ₀ δ ∈ 𝓝 τ₁ := isOpen_ball.mem_nhds hτ₁
  have hτ₁c : τ₁ ∈ closedBall τ₀ δ := ball_subset_closedBall hτ₁
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := 0)
    (b := 2 * π) (F := fun τ θ => f (τ + circleMap 0 ρ θ • v))
    (F' := fun τ θ => fderiv ℂ f (τ + circleMap 0 ρ θ • v)) (bound := fun _ => M) hs ?_ ?_ ?_ ?_ ?_
    ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [hs] with τ hτ
    exact (hcont τ (ball_subset_closedBall hτ)).aestronglyMeasurable
  · exact (hcont τ₁ hτ₁c).intervalIntegrable _ _
  · exact (hcd.comp_continuous (by fun_prop) (hmem τ₁ hτ₁c)).aestronglyMeasurable
  · refine Eventually.of_forall fun θ _ τ hτ => hM _ ⟨(τ, circleMap 0 ρ θ),
      ⟨ball_subset_closedBall hτ, circleMap_mem_sphere 0 hρ θ⟩, rfl⟩
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun θ _ τ hτ => ?_
    have h1 : HasFDerivAt f (fderiv ℂ f (τ + circleMap 0 ρ θ • v)) (τ + circleMap 0 ρ θ • v) :=
      (hf.differentiableAt (hO.mem_nhds (hmem τ (ball_subset_closedBall hτ) θ))).hasFDerivAt
    have h2 := h1.comp τ ((hasFDerivAt_id τ).add_const (circleMap 0 ρ θ • v))
    simpa [Function.comp_def] using h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
