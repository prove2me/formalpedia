-- Prove2me | solution 1 for ProjReflGrad.Adaptive.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:06:01.3389+00:00
-- url     : https://prove2.me/submissions/f304a393-96fc-41ee-9c48-f30f2b015380

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

set_option autoImplicit false

open ProjReflGrad.Adaptive in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (F : H → H) (α lamBar : ℝ) (hα : 0 ≤ α)
    (yp yh : H) (taup lamp : ℝ) (hlamp : 0 < lamp)
    (hge : lamp ≤ stepCap F α lamBar yp taup lamp yh 1) :
    ∃ l ∈ Set.Icc lamp (stepCap F α lamBar yp taup lamp yh 1),
      ‖l • F yh - lamp • F yp‖ ≤ α * ‖yh - yp‖ := by
  refine ⟨lamp, ⟨le_refl _, hge⟩, ?_⟩
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hlamp.le]
  by_cases hF : F yh = F yp
  · rw [hF, sub_self, norm_zero, mul_zero]
    positivity
  · have hpos : 0 < ‖F yh - F yp‖ := norm_pos_iff.2 (sub_ne_zero.2 hF)
    have h1 : lamp ≤ α * ‖yh - yp‖ / ‖F yh - F yp‖ := by
      refine le_trans hge ?_
      unfold stepCap
      rw [if_neg hF]
      exact min_le_left _ _
    rw [le_div_iff₀ hpos] at h1
    linarith
