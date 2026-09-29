-- Prove2me | solution 1 for WorkbookCorrected.cos_sq_double_angle_79936
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:50:52.450117+00:00
-- url     : https://prove2.me/submissions/5b6426a5-e759-4b14-9fbb-d62878c6e404

import Mathlib

theorem solution : ∀ x : ℝ, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  rw [Real.cos_sq]
  ring
