-- Prove2me | solution 1 for PiIrrationality.remainder_separation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T07:29:56.788255+00:00
-- url     : https://prove2.me/submissions/c939546a-0ef9-4b43-8941-79f123feb095

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (z y R U T : ℂ) (a t : ℝ)
    (hidentity : R - U = (z - y) * T)
    (ha : 0 < a) (ht : 0 < t)
    (hU : a ≤ ‖U‖) (hR : ‖R‖ ≤ a / 2) (hT : ‖T‖ < t) :
    a / (2 * t) < ‖z - y‖ := by
  have htriangle : ‖U‖ ≤ ‖R - U‖ + ‖R‖ := by
    calc
      ‖U‖ = ‖(R - U) - R‖ := by simp
      _ ≤ ‖R - U‖ + ‖R‖ := norm_sub_le _ _
  rw [hidentity, norm_mul] at htriangle
  have hproduct : a / 2 ≤ ‖z - y‖ * ‖T‖ := by linarith
  have hpositive : 0 < ‖z - y‖ := by
    by_contra h
    have hz : ‖z - y‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz, zero_mul] at hproduct
    linarith
  have hstrict := mul_lt_mul_of_pos_left hT hpositive
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) ht)).2
  nlinarith
