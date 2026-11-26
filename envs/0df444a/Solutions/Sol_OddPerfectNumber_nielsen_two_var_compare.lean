-- Prove2me | solution 1 for OddPerfectNumber.nielsen_two_var_compare
-- status  : ACCEPTED   (prove)
-- author  : @curiyu
-- created : 2026-09-08T04:25:28.835441+00:00
-- url     : https://prove2.me/submissions/1b8a8757-3f21-4a0d-8978-a3b1245ef4eb

import Mathlib

theorem solution (x1 x2 w : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hw0 : 0 < w) (hw1 : w < 1) :
    (1 - 1 / x1) * (1 - 1 / x2) ≥ (1 - 1 / (w * x1)) * (1 - 1 / (x2 / w)) ↔ w ≤ x2 / x1 := by
  have hden : 0 < w * x1 * x2 := by positivity
  have hw1' : 0 < 1 - w := by linarith
  have hdecomp : (1 - 1 / x1) * (1 - 1 / x2) - (1 - 1 / (w * x1)) * (1 - 1 / (x2 / w))
      = (1 - w) * (x2 - w * x1) / (w * x1 * x2) := by
    field_simp
    ring
  constructor
  · intro hge
    have h0 : 0 ≤ (1 - 1 / x1) * (1 - 1 / x2) - (1 - 1 / (w * x1)) * (1 - 1 / (x2 / w)) :=
      sub_nonneg.mpr hge
    rw [hdecomp] at h0
    have hN : 0 ≤ (1 - w) * (x2 - w * x1) := by
      have h00 := (le_div_iff₀ hden).mp h0
      rwa [zero_mul] at h00
    have hle : 0 ≤ x2 - w * x1 := by
      by_contra hcon
      push Not at hcon
      have hneg : (1 - w) * (x2 - w * x1) < 0 := mul_neg_of_pos_of_neg hw1' hcon
      linarith
    have hle2 : w * x1 ≤ x2 := by linarith
    rwa [le_div_iff₀ hx1]
  · intro hle
    rw [le_div_iff₀ hx1] at hle
    have hle2 : 0 ≤ x2 - w * x1 := by linarith
    have hN : 0 ≤ (1 - w) * (x2 - w * x1) := mul_nonneg (le_of_lt hw1') hle2
    have h0 : 0 ≤ (1 - w) * (x2 - w * x1) / (w * x1 * x2) :=
      div_nonneg hN (le_of_lt hden)
    rw [← hdecomp] at h0
    exact sub_nonneg.mp h0
