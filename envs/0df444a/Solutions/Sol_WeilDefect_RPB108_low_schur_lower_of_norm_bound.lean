-- Prove2me | solution 1 for WeilDefect.RPB108.low_schur_lower_of_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:56:08.142071+00:00
-- url     : https://prove2.me/submissions/62d3921b-b0f5-4f8c-a115-c81b101a6eec

import Theorems.Thm_WeilDefect_RPB108_inverse_quadratic_upper
import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (r : E) (k P native A : ℝ)
    (hk : 0 < k) (hT : ‖T‖ ≤ 1/k) (hr : ‖r‖^2 ≤ P)
    (hnative : A+P/k ≤ native) : A ≤ native-(inner ℂ r (T r)).re := by
  have hq := inverse_quadratic_upper T r k hT
  have hd := (div_le_div_iff_of_pos_right hk).mpr hr
  linarith
