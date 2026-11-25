-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.plurisubharmonicIffLeviNonneg_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:36.929211+00:00
-- url     : https://prove2.me/submissions/6159bc5a-9eaa-447b-aebe-a5409240375a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_Hc_apply
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_line_hasFDerivAt_g
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_line_hasFDerivAt_G__3d389c
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_line_contOn_H
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circ_smul
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_lap_nonneg_of_sub_mean
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_le_circleAverage_of_lap_nonneg


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
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution : IsPsh_iff_isLeviPshStatement := by
  intro D U φ hU hφ
  constructor
  · rintro ⟨-, hsub⟩
    refine ⟨hφ, fun z hz w => ?_⟩
    set V := {ζ : ℂ | z + ζ • w ∈ U} with hV
    have hVo : IsOpen V := hU.preimage (by fun_prop)
    have h0 : (0:ℂ) ∈ V := by simpa [V] using hz
    obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.mp hVo 0 h0
    have hR' : closedBall (0:ℂ) (R/2) ⊆ V := (closedBall_subset_ball (by linarith)).trans hR
    have key := lap_nonneg_of_sub_mean (V := V) (g := fun ζ => φ (z + ζ • w)) (G := Gc φ z w)
      (H := Hc φ z w) (fun ζ hζ => line_hasFDerivAt_g hU hφ z w hζ)
      (fun ζ hζ => line_hasFDerivAt_G hU hφ z w hζ) (line_contOn_H hU hφ z w)
      (by linarith : (0:ℝ) < R/2) hR' ?_
    · rw [Hc_apply, Hc_apply] at key
      simp only [zero_smul, add_zero, one_smul] at key
      unfold levi
      linarith
    · intro r hr
      have hmem : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • ((r:ℂ) • w) ∈ U := by
        intro ζ hζ
        rw [smul_smul]
        apply hR'
        rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr.1]
        nlinarith [norm_nonneg ζ, hr.2]
      have h1 := (hsub z ((r:ℂ) • w) hmem).2
      simp only [zero_smul, add_zero]
      convert h1 using 1
      rw [Real.circleAverage_def, Real.circleAverage_def]
      congr 1
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      simp only [circ_smul r θ w]
  · rintro ⟨-, hlev⟩
    refine ⟨hφ.continuousOn.upperSemicontinuousOn, fun z w hdisc => ?_⟩
    set V := {ζ : ℂ | z + ζ • w ∈ U} with hV
    have hB : closedBall (0:ℂ) 1 ⊆ V := fun ζ hζ => hdisc ζ (by simpa using hζ)
    have hcont : Continuous fun θ => φ (z + circleMap 0 1 θ • w) :=
      hφ.continuousOn.comp_continuous
        (continuous_const.add ((continuous_circleMap 0 1).smul continuous_const))
        (fun θ => hdisc _ (by simp))
    refine ⟨hcont.intervalIntegrable 0 (2*π), ?_⟩
    have key := le_circleAverage_of_lap_nonneg (V := V) (g := fun ζ => φ (z + ζ • w))
      (G := Gc φ z w) (H := Hc φ z w) (fun ζ hζ => line_hasFDerivAt_g hU hφ z w hζ)
      (fun ζ hζ => line_hasFDerivAt_G hU hφ z w hζ) (line_contOn_H hU hφ z w) zero_le_one hB ?_
    · simpa using key
    · intro x hx θ
      rw [Hc_apply, Hc_apply]
      have := hlev _ (hB hx) (circleMap 0 1 θ • w)
      unfold levi at this
      rw [smul_smul, mul_comm Complex.I] at this
      linarith
end ReciprocityTheory.AnForm.A.PshLap
