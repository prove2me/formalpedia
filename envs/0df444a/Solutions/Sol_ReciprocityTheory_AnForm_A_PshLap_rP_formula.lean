-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.rP_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:37.75084+00:00
-- url     : https://prove2.me/submissions/40320eb1-0bb1-41fa-8299-d3fa3f9cbf26

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_clm_circleMap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleMap_mem_closedBall
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_eq_integral_radial_second
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_angular_period
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_swap_cont
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_continuous_circleMap_uncurry
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_mapsTo_rect
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
theorem _root_.solution (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hGc : ContinuousOn G V)
    (hHc : ContinuousOn H V) {R r : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R)
    (hR : closedBall (0:ℂ) R ⊆ V) :
    r * Pr G r = ∫ s in (0:ℝ)..r, s * Lap H s := by
  have hr : closedBall (0:ℂ) r ⊆ V := (closedBall_subset_closedBall hrR).trans hR
  have hmem : ∀ s ∈ uIcc (0:ℝ) r, ∀ θ : ℝ, circleMap 0 s θ ∈ V := fun s hs θ => by
    rw [uIcc_of_le hr0] at hs
    exact hr (circleMap_mem_closedBall hs.1 hs.2)
  have hcG : ∀ s ∈ uIcc (0:ℝ) r, Continuous fun θ => G (circleMap 0 s θ) (circleMap 0 1 θ) :=
    fun s hs => (hGc.comp_continuous (continuous_circleMap 0 s) (hmem s hs)).clm_apply
      (continuous_circleMap 0 1)
  have hcH : ∀ s ∈ uIcc (0:ℝ) r, ∀ u : ℂ, Continuous fun θ =>
      H (circleMap 0 s θ) (circleMap 0 1 θ * u) (circleMap 0 1 θ * u) :=
    fun s hs u => ((hHc.comp_continuous (continuous_circleMap 0 s) (hmem s hs)).clm_apply
      ((continuous_circleMap 0 1).mul continuous_const)).clm_apply
      ((continuous_circleMap 0 1).mul continuous_const)
  have e1 : r * Pr G r = ∫ θ in (0:ℝ)..2*π, G (circleMap 0 r θ) (circleMap 0 r θ) := by
    unfold Pr
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [clm_circleMap (G (circleMap 0 r θ)) r θ]
  have e2 := intervalIntegral.integral_congr (μ := volume) (a := (0:ℝ)) (b := 2*π)
    (fun θ (_ : θ ∈ uIcc (0:ℝ) (2*π)) => eq_integral_radial_second hGd hGc hHc hr0 hr θ)
  have hcont : ContinuousOn (Function.uncurry fun s θ =>
      s * H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
        G (circleMap 0 s θ) (circleMap 0 1 θ)) (Icc 0 r ×ˢ Icc 0 (2*π)) := by
    refine ContinuousOn.add (ContinuousOn.mul continuous_fst.continuousOn ?_) (contOn_G hGc hr)
    exact ((hHc.comp continuous_circleMap_uncurry.continuousOn (mapsTo_rect hr)).clm_apply
      ((continuous_circleMap 0 1).comp continuous_snd).continuousOn).clm_apply
      ((continuous_circleMap 0 1).comp continuous_snd).continuousOn
  have e3 := swap_cont hr0 two_pi_pos.le hcont
  rw [e1, e2, ← e3]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  have hs' : closedBall (0:ℂ) |s| ⊆ V := by
    rw [uIcc_of_le hr0] at hs
    rw [abs_of_nonneg hs.1]
    exact (closedBall_subset_closedBall hs.2).trans hr
  have hH1 := hcH s hs 1
  simp only [mul_one] at hH1
  rw [intervalIntegral.integral_add ((hH1.const_mul s).intervalIntegrable _ _)
    ((hcG s hs).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    angular_period hGd hGc hHc hs', Lap, intervalIntegral.integral_add (hH1.intervalIntegrable _ _)
    ((hcH s hs Complex.I).intervalIntegrable _ _)]
  ring
end ReciprocityTheory.AnForm.A.PshLap
