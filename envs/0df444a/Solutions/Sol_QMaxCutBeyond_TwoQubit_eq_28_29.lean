-- Prove2me | solution 1 for QMaxCutBeyond.TwoQubit.eq_28_29
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:33:13.834766+00:00
-- url     : https://prove2.me/submissions/65ef9905-0802-4587-a5a9-a296e14cbe4e

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (11 / 20 : ℝ) * (2 + y + x) ≤ max (2 * y) (max (3 * x + 1) ((4 + x + y) / 3)) := by
  by_contra h
  rw [not_le, max_lt_iff, max_lt_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  linarith
