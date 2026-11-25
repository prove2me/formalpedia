-- Prove2me | solution 1 for PI.EF.Rect.rectInt_div_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:53:17.251633+00:00
-- url     : https://prove2.me/submissions/f6ede51d-1b3c-47cd-b981-cea4aff18e2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_ne_of_mem_bdry_of_mem_open
import Theorems.Thm_PI_EF_Rect_rectInt_inv_sub
import Theorems.Thm_PI_EF_Rect_rectInt_congr
import Theorems.Thm_PI_EF_Rect_rectInt_add
import Theorems.Thm_PI_EF_Rect_rectInt_const_mul
import Theorems.Thm_PI_EF_Rect_rectOpen_eq
import Theorems.Thm_PI_EF_Rect_rectClosed_mem_nhds
import Theorems.Thm_PI_EF_Rect_rectBdry_subset
import Theorems.Thm_PI_EF_Rect_le_of_mem_rectOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real
namespace PI.EF.Rect
theorem _root_.solution {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : DifferentiableOn ℂ h (rectClosed z w)) :
    rectInt (fun s => h s / (s - p)) z w = 2 * π * I * h p := by
  obtain ⟨hre, him⟩ := le_of_mem_rectOpen hp
  have hN := rectClosed_mem_nhds hp
  have hsub := rectBdry_subset hre him
  have hdc : ContinuousOn (dslope h p) (rectClosed z w) :=
    (continuousOn_dslope hN).2 ⟨hh.continuousOn, hh.differentiableAt hN⟩
  have hz : rectInt (dslope h p) z w = 0 := by
    have e : rectClosed z w = uIcc z.re w.re ×ℂ uIcc z.im w.im := by
      rw [rectClosed, uIcc_of_le hre, uIcc_of_le him]
    unfold rectInt
    refine Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ z w {p}
      (Set.countable_singleton p) (e ▸ hdc) ?_
    intro x hx
    rw [min_eq_left hre, max_eq_right hre, min_eq_left him, max_eq_right him] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxo : x ∈ rectOpen z w := by
      rw [rectOpen_eq]
      exact hx1
    exact (differentiableAt_dslope_of_ne hx2).2 (hh.differentiableAt (rectClosed_mem_nhds hxo))
  have hinv : ContinuousOn (fun s => h p * (s - p)⁻¹) (rectBdry z w) :=
    continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun s hs =>
      sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp))
  have hcong : EqOn (fun s => h s / (s - p)) (fun s => dslope h p s + h p * (s - p)⁻¹)
      (rectBdry z w) := by
    intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    simp only
    rw [dslope_of_ne _ (sub_ne_zero.1 hne), slope_def_field, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [rectInt_congr hcong, rectInt_add (hdc.mono hsub) hinv, hz, rectInt_const_mul,
    rectInt_inv_sub hp]
  ring
end PI.EF.Rect
