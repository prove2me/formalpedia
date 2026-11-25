-- Prove2me | solution 1 for PI.EF.Rect.rectInt_div_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:34.13009+00:00
-- url     : https://prove2.me/submissions/ae2e7046-ed89-42a9-af6a-94ec052d340e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_ne_of_mem_bdry_of_mem_open
import Theorems.Thm_PI_EF_Rect_rectInt_inv_sub_sq
import Theorems.Thm_PI_EF_Rect_rectInt_congr
import Theorems.Thm_PI_EF_Rect_rectInt_add
import Theorems.Thm_PI_EF_Rect_rectInt_const_mul
import Theorems.Thm_PI_EF_Rect_rectClosed_mem_nhds
import Theorems.Thm_PI_EF_Rect_rectBdry_subset
import Theorems.Thm_PI_EF_Rect_le_of_mem_rectOpen
import Theorems.Thm_PI_EF_Rect_continuousOn_div_sub
import Theorems.Thm_PI_EF_Rect_rectInt_div_sub

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
    rectInt (fun s => h s / (s - p) ^ 2) z w = 2 * π * I * deriv h p := by
  obtain ⟨hre, him⟩ := le_of_mem_rectOpen hp
  have hN := rectClosed_mem_nhds hp
  have hsub := rectBdry_subset hre him
  have hd : DifferentiableOn ℂ (dslope h p) (rectClosed z w) :=
    (Complex.differentiableOn_dslope hN).2 hh
  have hinv : ContinuousOn (fun s => h p * ((s - p) ^ 2)⁻¹) (rectBdry z w) :=
    continuousOn_const.mul (ContinuousOn.inv₀ ((continuousOn_id.sub continuousOn_const).pow 2)
      fun s hs => pow_ne_zero 2 (sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)))
  have hcong : EqOn (fun s => h s / (s - p) ^ 2)
      (fun s => dslope h p s / (s - p) + h p * ((s - p) ^ 2)⁻¹) (rectBdry z w) := by
    intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    simp only
    rw [dslope_of_ne _ (sub_ne_zero.1 hne), slope_def_field, div_div, ← sq, div_eq_mul_inv,
      div_eq_mul_inv]
    ring
  rw [rectInt_congr hcong, rectInt_add (continuousOn_div_sub hp (hd.continuousOn.mono hsub)) hinv,
    rectInt_div_sub hp hd, rectInt_const_mul, rectInt_inv_sub_sq hp, dslope_same]
  ring
end PI.EF.Rect
