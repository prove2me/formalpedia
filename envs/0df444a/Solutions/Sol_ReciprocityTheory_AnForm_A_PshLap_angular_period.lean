-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.angular_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:40.190071+00:00
-- url     : https://prove2.me/submissions/f12abe69-bccc-4563-b96b-932ae4dd9b2a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleMap_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hGc : ContinuousOn G V)
    (hHc : ContinuousOn H V) {s : ℝ} (hs : closedBall (0:ℂ) |s| ⊆ V) :
    ∫ θ in (0:ℝ)..2*π, G (circleMap 0 s θ) (circleMap 0 1 θ) =
      s * ∫ θ in (0:ℝ)..2*π, H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I)
        (circleMap 0 1 θ * Complex.I) := by
  have hmem : ∀ θ : ℝ, circleMap 0 s θ ∈ V := fun θ => hs (by simp)
  have hc1 : Continuous fun θ => G (circleMap 0 s θ) (circleMap 0 1 θ) :=
    (hGc.comp_continuous (continuous_circleMap 0 s) hmem).clm_apply (continuous_circleMap 0 1)
  have hc2 : Continuous fun θ => H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I)
      (circleMap 0 1 θ * Complex.I) :=
    ((hHc.comp_continuous (continuous_circleMap 0 s) hmem).clm_apply
      ((continuous_circleMap 0 1).mul continuous_const)).clm_apply
      ((continuous_circleMap 0 1).mul continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => G (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I))
    (f' := fun θ => s * H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I)
        (circleMap 0 1 θ * Complex.I) - G (circleMap 0 s θ) (circleMap 0 1 θ))
    (a := 0) (b := 2 * π)
    (fun θ _ => by
      have h1 := ((hGd _ (hmem θ)).comp_hasDerivAt θ (hasDerivAt_circleMap 0 s θ)).clm_apply
        ((hasDerivAt_circleMap 0 1 θ).mul_const Complex.I)
      refine h1.congr_deriv ?_
      simp only [Function.comp_def]
      have e1 : circleMap 0 s θ * Complex.I = s • (circleMap 0 1 θ * Complex.I) := by
        rw [circleMap_eq_smul s θ, smul_mul_assoc]
      have e2 : circleMap 0 1 θ * Complex.I * Complex.I = - circleMap 0 1 θ := by
        rw [mul_assoc, Complex.I_mul_I]; ring
      rw [e1, e2, map_smul, map_neg]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring) (((hc2.const_mul s).sub hc1).intervalIntegrable 0 (2 * π))
  have hp : circleMap 0 s (2 * π) = circleMap 0 s 0 := by
    simpa using periodic_circleMap 0 s 0
  have hp1 : circleMap 0 1 (2 * π) = circleMap 0 1 0 := by
    simpa using periodic_circleMap 0 1 0
  simp only [hp, hp1, sub_self] at h
  rw [intervalIntegral.integral_sub ((hc2.const_mul s).intervalIntegrable _ _)
    (hc1.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at h
  linarith
end ReciprocityTheory.AnForm.A.PshLap
