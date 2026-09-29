-- Prove2me | solution 1 for WorkbookCorrected.plus_80081
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T21:32:57.717928+00:00
-- url     : https://prove2.me/submissions/ad5d1291-1308-4606-adda-4ae065ccf83b

import Mathlib

theorem solution : ∀ k : ℕ, (0 : ℝ) ≤ |(Real.log k)/k^2| := by
  intro k
  exact abs_nonneg _
