-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ParametricCircleIntegralAnalytic_proof_7752f933dcaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:57.23308+00:00
-- url     : https://prove2.me/submissions/c1c9e3db-e571-4a7b-a471-8f6692bb18d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParametricCircleIntegralAnalytic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ParametricCircleIntegralAnalytic_analyticOnNhd_of_differentiableOn_fd_37006865feb4

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
open ParametricCircleIntegralAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ParametricCircleIntegralAnalytic
theorem _root_.solution : ParametricCircleIntegralAnalytic.Statement := by
  intro ι _ Φ O U c r hr hO hU hΦ hUO x₀ hx₀
  have hcd : ContinuousOn (fderiv ℂ Φ) O :=
    ((analyticOnNhd_of_differentiableOn_fd hO hΦ).contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hO le_rfl
  obtain ⟨u, v, hu, -, hx₀u, hsv, huv⟩ := generalized_tube_lemma isCompact_singleton (isCompact_sphere c r) hO
    (by rintro ⟨x, s⟩ ⟨hx, hs⟩; obtain rfl : x = x₀ := hx; exact hUO x hx₀ s hs)
  obtain ⟨ε, hε, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds (hx₀u rfl))
  have hK : closedBall x₀ ε ×ˢ sphere c r ⊆ O := fun p hp => huv ⟨hεu hp.1, hsv hp.2⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x₀ ε).prod (isCompact_sphere c r)).exists_bound_of_continuousOn
    (hcd.mono hK)
  have hmem : ∀ x ∈ closedBall x₀ ε, ∀ θ : ℝ, (x, circleMap c r θ) ∈ O := fun x hx θ =>
    hK ⟨hx, circleMap_mem_sphere c hr θ⟩
  have hcont : ∀ x ∈ closedBall x₀ ε,
      Continuous fun θ : ℝ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ) := fun x hx =>
    (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
      (hΦ.continuousOn.comp_continuous (by fun_prop) (hmem x hx))
  have hdiff : DifferentiableOn ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) (ball x₀ ε) := by
    intro x₁ hx₁
    have hs : ball x₀ ε ∈ 𝓝 x₁ := isOpen_ball.mem_nhds hx₁
    have hx₁c : x₁ ∈ closedBall x₀ ε := ball_subset_closedBall hx₁
    simp only [circleIntegral, deriv_circleMap]
    refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := 0)
      (b := 2 * π) (F := fun x θ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ))
      (F' := fun x θ => (circleMap 0 r θ * I) •
        (fderiv ℂ Φ (x, circleMap c r θ)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ))
      (bound := fun _ => |r| * (M * ‖ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ‖)) hs ?_ ?_ ?_ ?_ ?_
      ?_).differentiableAt.differentiableWithinAt
    · filter_upwards [hs] with x hx
      exact (hcont x (ball_subset_closedBall hx)).aestronglyMeasurable
    · exact (hcont x₁ hx₁c).intervalIntegrable _ _
    · refine Continuous.aestronglyMeasurable ?_
      exact (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
        ((ContinuousLinearMap.compL ℂ (ι → ℂ) ((ι → ℂ) × ℂ) ℂ).flip
          (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ) |>.continuous.comp
          (hcd.comp_continuous (by fun_prop) (hmem x₁ hx₁c)))
    · refine Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact hM _ ⟨ball_subset_closedBall hx, circleMap_mem_sphere c hr θ⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ x hx => ?_
      have h1 : HasFDerivAt Φ (fderiv ℂ Φ (x, circleMap c r θ)) (x, circleMap c r θ) :=
        (hΦ.differentiableAt (hO.mem_nhds (hmem x (ball_subset_closedBall hx) θ))).hasFDerivAt
      exact (h1.comp x (hasFDerivAt_prodMk_left x (circleMap c r θ))).const_smul (circleMap 0 r θ * I)
  exact analyticOnNhd_of_differentiableOn_fd isOpen_ball hdiff x₀ (mem_ball_self hε)
end ParametricCircleIntegralAnalytic
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
