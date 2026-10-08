-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootFinalAlgebraicNormalization
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T06:53:28.995843+00:00
-- url     : https://prove2.me/submissions/0d06ce4f-c89e-46d7-ab0c-e01d3d244328

import Mathlib

theorem solution
    (J S P : ℝ)
    (hbalance : 2 * J = 2 * Real.pi * (S - P)) :
    J / Real.pi = S - P := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  nlinarith [hbalance]
