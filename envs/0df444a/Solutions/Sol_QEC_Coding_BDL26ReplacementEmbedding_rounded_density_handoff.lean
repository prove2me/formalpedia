-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rounded_density_handoff
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T14:54:14.672053+00:00
-- url     : https://prove2.me/submissions/b91eb50a-45fe-47ff-a5a1-d3d84fcd28e3

import Mathlib

/-- Replacement embedding: handing the rounded density over to the exact one. -/
theorem solution {L ell coefficient : ℝ} (hL : 13 ≤ L) (hell : 0 ≤ ell)
    (hround : ell ≤ L + 2) (hcoefficient : 0 ≤ coefficient) :
    48 * coefficient * ell ^ 2 ≤ 64 * coefficient * L ^ 2 := by
  have h1 : ell ^ 2 ≤ (L + 2) ^ 2 := by nlinarith
  have h2 : 3 * (L + 2) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  nlinarith [h1, h2, hcoefficient]
