-- Prove2me | solution 1 for ProjReflGrad.Adaptive.stepCap_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:06:00.036334+00:00
-- url     : https://prove2.me/submissions/f2966af9-2027-4de2-854f-ae8efcfcc6bb

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

set_option autoImplicit false

open ProjReflGrad.Adaptive in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (F : H → H) (L : ℝ) (hL : 0 < L)
    (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L) (α lamBar : ℝ) (hα : 0 < α) (yp y : H) (taup lamp tau : ℝ)
    (htaup : 0 ≤ taup) (htau : tau ∈ Set.Ioc 0 1) (hlamp : α / L ≤ lamp)
    (hbar : α / L ≤ lamBar) :
    α / L ≤ stepCap F α lamBar yp taup lamp y tau := by
  obtain ⟨ht0, ht1⟩ := htau
  have h2 : α / L ≤ (1 + taup) / tau * lamp := by
    have : 1 ≤ (1 + taup) / tau := by
      rw [le_div_iff₀ ht0]; linarith
    have hl : 0 ≤ lamp := le_trans (by positivity) hlamp
    nlinarith
  unfold stepCap
  split_ifs with hF
  · exact le_min h2 hbar
  · refine le_min ?_ (le_min h2 hbar)
    have hpos : 0 < ‖F y - F yp‖ := norm_pos_iff.2 (sub_ne_zero.2 hF)
    have hyy : y ≠ yp := fun h => hF (by rw [h])
    have hpos2 : 0 < ‖y - yp‖ := norm_pos_iff.2 (sub_ne_zero.2 hyy)
    rw [div_le_div_iff₀ hL hpos]
    have := hC3 y yp
    nlinarith
