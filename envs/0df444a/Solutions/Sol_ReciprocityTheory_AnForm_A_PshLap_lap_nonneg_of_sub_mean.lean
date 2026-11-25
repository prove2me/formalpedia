-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.lap_nonneg_of_sub_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:51.273808+00:00
-- url     : https://prove2.me/submissions/07b2407c-0161-4d27-aefe-7bd47ddbc7ec

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_rot_id
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleAverage_sub_le

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
    (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall (0:ℂ) R ⊆ V)
    (hsub : ∀ r ∈ Ioc (0:ℝ) R, g 0 ≤ Real.circleAverage g 0 r) :
    0 ≤ H 0 1 1 + H 0 Complex.I Complex.I := by
  by_contra hc
  push_neg at hc
  set c := H 0 1 1 + H 0 Complex.I Complex.I with hcdef
  have h0V : (0:ℂ) ∈ V := hR (mem_closedBall_self hR0.le)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (hHc 0 h0V) (-c/4) (by linarith)
  set ρ := min (δ/2) R with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) hR0
  have hρR : ρ ≤ R := min_le_right _ _
  have hK : ∀ x ∈ closedBall (0:ℂ) ρ, ∀ θ : ℝ, H x (circleMap 0 1 θ) (circleMap 0 1 θ) +
      H x (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I) ≤ c / 2 := by
    intro x hx θ
    have hxV : x ∈ V := hR (closedBall_subset_closedBall hρR hx)
    have hd : dist x 0 < δ :=
      lt_of_le_of_lt (mem_closedBall.mp hx) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have hn : ‖H x - H 0‖ < -c/4 := by simpa [dist_eq_norm] using hball hxV hd
    have hrot := rot_id (H 0) θ
    have he : ‖circleMap 0 1 θ‖ = 1 := by simp
    have heI : ‖circleMap 0 1 θ * Complex.I‖ = 1 := by simp
    have b1 : |(H x - H 0) (circleMap 0 1 θ) (circleMap 0 1 θ)| ≤ ‖H x - H 0‖ := by
      have := (H x - H 0).le_opNorm₂ (circleMap 0 1 θ) (circleMap 0 1 θ)
      rw [he] at this; simpa [Real.norm_eq_abs] using this
    have b2 : |(H x - H 0) (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I)| ≤
        ‖H x - H 0‖ := by
      have := (H x - H 0).le_opNorm₂ (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I)
      rw [heI] at this; simpa [Real.norm_eq_abs] using this
    simp only [ContinuousLinearMap.sub_apply] at b1 b2
    have := abs_le.mp b1
    have := abs_le.mp b2
    linarith
  have h1 := circleAverage_sub_le hg hGd hHc hρ.le
    ((closedBall_subset_closedBall hρR).trans hR) (c/2) hK
  have h2 := hsub ρ ⟨hρ, hρR⟩
  have h3 : c / 2 * ρ ^ 2 / 4 < 0 := by
    have : 0 < ρ ^ 2 := by positivity
    nlinarith
  linarith
end ReciprocityTheory.AnForm.A.PshLap
