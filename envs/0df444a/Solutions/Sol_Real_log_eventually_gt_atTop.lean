-- Prove2me | solution 1 for Real.log_eventually_gt_atTop
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:23:58.777521+00:00
-- url     : https://prove2.me/submissions/269e1024-c2f8-4b41-a341-ed7fcbfee79e

import Mathlib.Analysis.SumIntegralComparisons

open Filter

theorem solution (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x := by
  exact Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)
