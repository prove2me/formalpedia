-- Prove2me | solution 1 for ShapleyNV.two_by_two_no_saddle
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:36:19.790202+00:00
-- url     : https://prove2.me/submissions/662114d1-48cc-426f-94f8-72d640773b1a

import Mathlib

open MeasureTheory NNReal ENNReal

theorem solution (a b c d : ℝ)
    (h : max (min a c) (min b d) ≠ min (max a b) (max c d)) :
    max a d < min b c ∨ max b c < min a d := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  apply h
  simp only [max_def, min_def] at h1 h2 ⊢
  split_ifs at h1 h2 ⊢ <;> linarith
