-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.mean_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:41.526638+00:00
-- url     : https://prove2.me/submissions/47e40757-73b0-485e-8ca3-8c971381dc04

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleMap_mem_closedBall
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_radial_ftc
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_swap_cont
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_contOn_G

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (hg : ∀ x ∈ V, HasFDerivAt g (G x) x) (hGc : ContinuousOn G V) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : closedBall (0:ℂ) R ⊆ V) :
    Real.circleAverage g 0 R - g 0 = (2*π)⁻¹ * ∫ r in (0:ℝ)..R, Pr G r := by
  have hgc : Continuous fun θ => g (circleMap 0 R θ) := by
    have : ContinuousOn g V := fun x hx => (hg x hx).continuousAt.continuousWithinAt
    exact this.comp_continuous (continuous_circleMap 0 R)
      (fun θ => hR (circleMap_mem_closedBall hR0 le_rfl))
  have h1 : ∫ θ in (0:ℝ)..2*π, (g (circleMap 0 R θ) - g 0) =
      ∫ θ in (0:ℝ)..2*π, ∫ r in (0:ℝ)..R, G (circleMap 0 r θ) (circleMap 0 1 θ) :=
    intervalIntegral.integral_congr (fun θ _ => radial_ftc hg hGc hR0 hR θ)
  have h2 : ∫ θ in (0:ℝ)..2*π, (g (circleMap 0 R θ) - g 0) =
      (∫ θ in (0:ℝ)..2*π, g (circleMap 0 R θ)) - 2 * π * g 0 := by
    rw [intervalIntegral.integral_sub (hgc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have h3 := swap_cont (F := fun r θ => G (circleMap 0 r θ) (circleMap 0 1 θ)) hR0
    two_pi_pos.le (contOn_G hGc hR)
  have h4 : (2*π)⁻¹ * (2 * π * g 0) = g 0 := by field_simp
  rw [Real.circleAverage_def, smul_eq_mul]
  unfold Pr
  rw [h3, ← h1, h2, mul_sub, h4]
end ReciprocityTheory.AnForm.A.PshLap
