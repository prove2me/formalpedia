-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.circle_mean
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:28.305636+00:00
-- url     : https://prove2.me/submissions/aa0bf075-0685-4d5e-8113-353af526b422

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, u (c + Complex.exp ((θ : ℂ) * I) • w) =
      ((2 * Real.pi : ℝ) : ℂ) * u c := by
  by_cases hw0 : w = 0
  · subst hw0
    simp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hρ1 : 1 < R / ‖w‖ := by
    rw [lt_div_iff₀ hwpos]
    linarith
  have hg : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.ball 0 (R / ‖w‖)) := by
    intro ζ hζ
    have hmem : c + ζ • w ∈ ball c R := by
      rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hwpos] at hζ
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact hζ
    have h1 : DifferentiableAt ℂ u (c + ζ • w) := hu.differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => c + ζ • w) ζ :=
      (differentiableAt_id.smul_const w).const_add c
    exact (h1.comp ζ h2).differentiableWithinAt
  have hcl : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.closedBall 0 1) :=
    hg.mono (Metric.closedBall_subset_ball hρ1)
  have key := hcl.circleIntegral_sub_inv_smul (w := 0) (by simp)
  simp only [circleIntegral, deriv_circleMap, sub_zero, smul_eq_mul, zero_smul, add_zero] at key
  have hcm : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp ((θ : ℂ) * I) := by
    intro θ
    simp [circleMap]
  have h3 : ∀ θ : ℝ, circleMap 0 1 θ * I * ((circleMap 0 1 θ)⁻¹ * u (c + circleMap 0 1 θ • w)) =
      I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by
    intro θ
    have hne : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
    rw [hcm θ] at hne ⊢
    calc Complex.exp ((θ : ℂ) * I) * I * ((Complex.exp ((θ : ℂ) * I))⁻¹ * u (c + Complex.exp ((θ : ℂ) * I) • w))
        = I * u (c + Complex.exp ((θ : ℂ) * I) • w) * (Complex.exp ((θ : ℂ) * I) * (Complex.exp ((θ : ℂ) * I))⁻¹) := by ring
      _ = I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by rw [mul_inv_cancel₀ hne, mul_one]
  simp only [h3, intervalIntegral.integral_const_mul] at key
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [key]
  push_cast
  ring
end ReciprocityTheory.L2DbarEstimates.C
