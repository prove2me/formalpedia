-- Prove2me | solution 1 for TwoDegenerateGraphs.entropyTangentCoefficient_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/b648bd5f-8d1a-494b-830d-ced4fe829e58

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (q : ℝ) :
    entropyTangentZeroCoefficient q ^ 2 +
        entropyTangentOneCoefficient q ^ 2 =
      1 + (2 * q - 1) ^ 2 / 4 := by
  unfold entropyTangentZeroCoefficient entropyTangentOneCoefficient
  calc
    (Real.sqrt 2 * (3 - 2 * q) / 4) ^ 2 +
        (Real.sqrt 2 * (1 + 2 * q) / 4) ^ 2 =
      (Real.sqrt 2) ^ 2 *
        (((3 - 2 * q) ^ 2 + (1 + 2 * q) ^ 2) / 16) := by ring
    _ = 1 + (2 * q - 1) ^ 2 / 4 := by
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring
end TwoDegenerateGraphs
