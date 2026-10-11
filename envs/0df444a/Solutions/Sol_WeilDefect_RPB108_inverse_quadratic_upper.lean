-- Prove2me | solution 1 for WeilDefect.RPB108.inverse_quadratic_upper
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:54:51.092323+00:00
-- url     : https://prove2.me/submissions/b6ad6ad7-ccc2-4fd3-bcf5-9a6bfc89b0b2

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (r : E) (k : ℝ)
    (hT : ‖T‖ ≤ 1/k) :
    (inner ℂ r (T r)).re ≤ ‖r‖^2/k := by
  have ht : ‖T r‖ ≤ (1/k)*‖r‖ :=
    (T.le_opNorm r).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  calc
    (inner ℂ r (T r)).re ≤ ‖inner ℂ r (T r)‖ := Complex.re_le_norm _
    _ ≤ ‖r‖*‖T r‖ := norm_inner_le_norm _ _
    _ ≤ ‖r‖*((1/k)*‖r‖) := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = ‖r‖^2/k := by ring
