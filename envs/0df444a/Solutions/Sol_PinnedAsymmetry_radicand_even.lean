-- Prove2me | solution 1 for PinnedAsymmetry.radicand_even
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T22:32:21.249978+00:00
-- url     : https://prove2.me/submissions/efd01838-1207-4106-935e-3fa83ccaf381

import Mathlib

open Real

theorem solution (K c β q : ℝ) :
    (β * c * sin (-q)) ^ 2 + K + 2 * c * (1 - cos (-q))
      = (β * c * sin q) ^ 2 + K + 2 * c * (1 - cos q) := by
  rw [sin_neg, cos_neg]; ring
