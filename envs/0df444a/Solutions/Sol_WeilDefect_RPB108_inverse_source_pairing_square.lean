-- Prove2me | solution 1 for WeilDefect.RPB108.inverse_source_pairing_square
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:26:44.418067+00:00
-- url     : https://prove2.me/submissions/b8cba334-c287-48ac-991f-cedd1743915a

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (r v : E) (P k : ℝ)
    (hk : 0 < k) (hT : ‖T‖ ≤ 1/k) (hr : ‖r‖^2 ≤ P) :
    ‖inner ℂ r (T v)‖^2 ≤ (P/k^2)*‖v‖^2 := by
  have ht : ‖T v‖ ≤ (1/k)*‖v‖ :=
    (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hi : ‖inner ℂ r (T v)‖ ≤ ‖r‖*((1/k)*‖v‖) :=
    (norm_inner_le_norm r (T v)).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
  have hn : 0 ≤ ‖r‖*((1/k)*‖v‖) := by positivity
  have hs : ‖inner ℂ r (T v)‖^2 ≤ (‖r‖*((1/k)*‖v‖))^2 := by
    nlinarith only [hi, hn, norm_nonneg (inner ℂ r (T v))]
  calc
    ‖inner ℂ r (T v)‖^2 ≤ (‖r‖*((1/k)*‖v‖))^2 := hs
    _ = ‖r‖^2*((1/k)^2*‖v‖^2) := by ring
    _ ≤ P*((1/k)^2*‖v‖^2) := mul_le_mul_of_nonneg_right hr (by positivity)
    _ = (P/k^2)*‖v‖^2 := by ring
