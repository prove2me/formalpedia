-- Prove2me | solution 1 for TwoDegenerateGraphs.entropyTangentOneCoefficient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/7a03885d-5701-4894-a3e2-d956dad96bea

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_sqrt_three_mul_entropyTangentRho

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (q : ℝ) :
    (1 - q) ^ 2 / (3 * entropyTangentSigma) +
        q ^ 2 / entropyTangentSigma +
        2 * q * (1 - q) /
          (Real.sqrt 3 * entropyTangentRho) =
      entropyTangentOneCoefficient q := by
  rw [sqrt_three_mul_entropyTangentRho]
  unfold entropyTangentSigma entropyTangentOneCoefficient
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [htwo]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
end TwoDegenerateGraphs
