-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_slice_cauchy_2d945a37a135
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:30.773342+00:00
-- url     : https://prove2.me/submissions/4e450407-29b0-451b-a13d-a5b3e8d754b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic

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
theorem _root_.solution {R ρ : ℝ} {ψ h : ℂ → ℂ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hψ : DifferentiableOn ℂ ψ (ball 0 R)) (hsph : ∀ z ∈ sphere (0 : ℂ) ρ, ψ z ≠ 0) (hψ0 : ψ 0 ≠ 0)
    (hh : ∀ z ∈ ball (0 : ℂ) R, ψ z ≠ 0 → DifferentiableAt ℂ h z)
    (hb : ∀ z ∈ ball (0 : ℂ) R, ∃ N ∈ 𝓝 z, ∃ C, ∀ w ∈ N, w ∈ ball (0 : ℂ) R → ψ w ≠ 0 → ‖h w‖ ≤ C) :
    (2 * π * I : ℂ)⁻¹ • (∮ z in C(0, ρ), z⁻¹ • h z) = h 0 := by
  classical
  have hψa : AnalyticOnNhd ℂ ψ (ball 0 R) := hψ.analyticOnNhd isOpen_ball
  have h0R : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self (hρ.trans hρR)
  have hiso : ∀ z₀ ∈ ball (0 : ℂ) R, ∀ᶠ z in 𝓝[≠] z₀, ψ z ≠ 0 := by
    intro z₀ hz₀
    rcases (hψa z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero with h' | h'
    · exact absurd (hψa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 R).isPreconnected
        hz₀ h' h0R) hψ0
    · exact h'
  set H : ℂ → ℂ := fun z => if ψ z = 0 then limUnder (𝓝[≠] z) h else h z with hH
  have hHd : ∀ z₀ ∈ ball (0 : ℂ) R, DifferentiableAt ℂ H z₀ := by
    intro z₀ hz₀
    by_cases hz : ψ z₀ = 0
    · obtain ⟨N, hN, C, hC⟩ := hb z₀ hz₀
      have hev : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → ψ z ≠ 0 := eventually_nhdsWithin_iff.mp (hiso z₀ hz₀)
      have hsn : N ∩ ball (0 : ℂ) R ∩ {z | z ≠ z₀ → ψ z ≠ 0} ∈ 𝓝 z₀ :=
        inter_mem (inter_mem hN (isOpen_ball.mem_nhds hz₀)) hev
      have hdiff : DifferentiableOn ℂ (Function.update h z₀ (limUnder (𝓝[≠] z₀) h))
          (N ∩ ball (0 : ℂ) R ∩ {z | z ≠ z₀ → ψ z ≠ 0}) := by
        refine Complex.differentiableOn_update_limUnder_of_bddAbove hsn ?_ ?_
        · intro z hz'
          exact (hh z hz'.1.1.2 (hz'.1.2 hz'.2)).differentiableWithinAt
        · refine ⟨C, ?_⟩
          rintro _ ⟨z, hz', rfl⟩
          exact hC z hz'.1.1.1 hz'.1.1.2 (hz'.1.2 hz'.2)
      have heq : H =ᶠ[𝓝 z₀] Function.update h z₀ (limUnder (𝓝[≠] z₀) h) := by
        filter_upwards [hev] with z hz'
        by_cases hzz : z = z₀
        · subst hzz
          simp [hH, hz]
        · simp [hH, hz' hzz, Function.update_of_ne hzz]
      exact (hdiff.differentiableAt hsn).congr_of_eventuallyEq heq
    · have hev : ∀ᶠ z in 𝓝 z₀, ψ z ≠ 0 := (hψa z₀ hz₀).continuousAt.eventually_ne hz
      have heq : H =ᶠ[𝓝 z₀] h := by
        filter_upwards [hev] with z hz'
        simp [hH, hz']
      exact (hh z₀ hz₀ hz).congr_of_eventuallyEq heq
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have hC := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := ∅) countable_empty (mem_ball_self hρ)
    (fun z hz => (hHd z (hcl hz)).continuousAt.continuousWithinAt)
    (fun z hz => hHd z (hcl (ball_subset_closedBall hz.1)))
  have hH0 : H 0 = h 0 := by simp [hH, hψ0]
  rw [← hH0, ← hC]
  congr 1
  refine circleIntegral.integral_congr hρ.le fun z hz => ?_
  simp [hH, hsph z hz]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
