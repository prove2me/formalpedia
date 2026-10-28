-- Prove2me | solution 1 for StrategyproofMinimax.Circle.line_center_split
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:16:02.59484+00:00
-- url     : https://prove2.me/submissions/760e7de5-99ca-4890-b2e2-cc8f573735ee

import Mathlib

theorem solution (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |x - 1 / 2| ≤ y * |x - (0 + y) / 2| + (1 - y) * |x - (y + 1) / 2| := by
  obtain ⟨hy0, hy1⟩ := hy
  have h1 : 0 ≤ 1 - y := by linarith
  have e : x - 1 / 2 = y * (x - (0 + y) / 2) + (1 - y) * (x - (y + 1) / 2) := by ring
  calc |x - 1 / 2| = |y * (x - (0 + y) / 2) + (1 - y) * (x - (y + 1) / 2)| := by rw [← e]
    _ ≤ |y * (x - (0 + y) / 2)| + |(1 - y) * (x - (y + 1) / 2)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hy0, abs_of_nonneg h1]
