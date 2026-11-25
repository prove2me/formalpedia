-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.circleAverage_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:21.641507+00:00
-- url     : https://prove2.me/submissions/f9616875-4cb6-4480-8d8a-55672b44a13d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleMap_mem_closedBall
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_intervalIntegrable_param
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_contOn_G
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_mean_formula
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_rP_formula
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_contOn_H

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
    (hR : closedBall (0:ℂ) R ⊆ V) (K : ℝ)
    (hK : ∀ x ∈ closedBall (0:ℂ) R, ∀ θ : ℝ, H x (circleMap 0 1 θ) (circleMap 0 1 θ) +
      H x (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I) ≤ K) :
    Real.circleAverage g 0 R - g 0 ≤ K * R ^ 2 / 4 := by
  have hGc : ContinuousOn G V := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
  rw [mean_formula hg hGc hR0 hR]
  have hPint : IntervalIntegrable (Pr G) volume 0 R :=
    intervalIntegrable_param hR0 two_pi_pos.le (contOn_G hGc hR)
  have hb : ∀ r ∈ Ioc (0:ℝ) R, Pr G r ≤ π * K * r := by
    intro r hr
    have hrV : closedBall (0:ℂ) r ⊆ V := (closedBall_subset_closedBall hr.2).trans hR
    have h1 := rP_formula hGd hGc hHc hr.1.le hr.2 hR
    have hLapInt : IntervalIntegrable (Lap H) volume 0 r :=
      intervalIntegrable_param hr.1.le two_pi_pos.le (contOn_H hHc hrV)
    have h2 : ∫ s in (0:ℝ)..r, s * Lap H s ≤ ∫ s in (0:ℝ)..r, s * (2 * π * K) := by
      refine intervalIntegral.integral_mono_on hr.1.le ?_ ?_ (fun s hs => ?_)
      · exact hLapInt.continuousOn_mul continuousOn_id
      · exact (continuous_id.mul continuous_const).intervalIntegrable _ _
      · refine mul_le_mul_of_nonneg_left ?_ hs.1
        have hK' : ∫ θ in (0:ℝ)..2*π, K = 2 * π * K := by simp
        rw [← hK']
        unfold Lap
        have hmem : ∀ θ : ℝ, circleMap 0 s θ ∈ V := fun θ =>
          hrV (circleMap_mem_closedBall hs.1 hs.2)
        have hc := hHc.comp_continuous (continuous_circleMap 0 s) hmem
        have he := continuous_circleMap 0 1
        refine intervalIntegral.integral_mono_on two_pi_pos.le ?_ intervalIntegrable_const
          (fun θ _ => hK _ (circleMap_mem_closedBall hs.1 (hs.2.trans hr.2)) θ)
        exact (((hc.clm_apply he).clm_apply he).add
          ((hc.clm_apply (he.mul continuous_const)).clm_apply
            (he.mul continuous_const))).intervalIntegrable _ _
    have h3 : ∫ s in (0:ℝ)..r, s * (2 * π * K) = π * K * r ^ 2 := by
      rw [intervalIntegral.integral_mul_const, integral_id]; ring
    have h4 : r * Pr G r ≤ r * (π * K * r) := by nlinarith
    exact le_of_mul_le_mul_left h4 hr.1
  have h4 : ∫ r in (0:ℝ)..R, Pr G r ≤ ∫ r in (0:ℝ)..R, π * K * r := by
    rw [intervalIntegral.integral_of_le hR0, intervalIntegral.integral_of_le hR0]
    exact setIntegral_mono_on hPint.1
      ((continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      measurableSet_Ioc hb
  have h5 : ∫ r in (0:ℝ)..R, π * K * r = π * K * R ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [h5] at h4
  have h6 : (2*π)⁻¹ * ∫ r in (0:ℝ)..R, Pr G r ≤ (2*π)⁻¹ * (π * K * R ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  calc _ ≤ _ := h6
    _ = K * R ^ 2 / 4 := by field_simp; ring
end ReciprocityTheory.AnForm.A.PshLap
