-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.le_circleAverage_of_lap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:25.415302+00:00
-- url     : https://prove2.me/submissions/17e6b66a-f33a-4ba5-9722-a3fbef64d9c5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleMap_mem_closedBall
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_mean_formula
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_rP_formula

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
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (hg : ∀ x ∈ V, HasFDerivAt g (G x) x)
    (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : closedBall (0:ℂ) R ⊆ V)
    (hpos : ∀ x ∈ closedBall (0:ℂ) R, ∀ θ : ℝ, 0 ≤ H x (circleMap 0 1 θ) (circleMap 0 1 θ) +
      H x (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I)) :
    g 0 ≤ Real.circleAverage g 0 R := by
  have hGc : ContinuousOn G V := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
  have hm := mean_formula hg hGc hR0 hR
  have hP : 0 ≤ ∫ r in (0:ℝ)..R, Pr G r := by
    rw [intervalIntegral.integral_of_le hR0]
    refine setIntegral_nonneg measurableSet_Ioc (fun r hr => ?_)
    have h1 := rP_formula hGd hGc hHc hr.1.le hr.2 hR
    have h2 : 0 ≤ ∫ s in (0:ℝ)..r, s * Lap H s := by
      refine intervalIntegral.integral_nonneg hr.1.le (fun s hs => mul_nonneg hs.1 ?_)
      exact intervalIntegral.integral_nonneg two_pi_pos.le
        (fun θ _ => hpos _ (circleMap_mem_closedBall hs.1 (hs.2.trans hr.2)) θ)
    rw [← h1] at h2
    exact (mul_nonneg_iff_of_pos_left hr.1).mp h2
  have : 0 ≤ (2*π)⁻¹ * ∫ r in (0:ℝ)..R, Pr G r := mul_nonneg (by positivity) hP
  linarith
end ReciprocityTheory.AnForm.A.PshLap
