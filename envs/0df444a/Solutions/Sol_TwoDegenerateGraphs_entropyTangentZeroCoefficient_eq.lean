-- Prove2me | solution 1 for TwoDegenerateGraphs.entropyTangentZeroCoefficient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/96b908ff-6db7-495a-afc2-8f9d5510eb49

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_sqrt_three_mul_entropyTangentRho

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (q : ℝ) :
    (1 - q) ^ 2 / entropyTangentSigma +
        q ^ 2 / (3 * entropyTangentSigma) +
        2 * q * (1 - q) /
          (Real.sqrt 3 * entropyTangentRho) =
      entropyTangentZeroCoefficient q := by
  rw [sqrt_three_mul_entropyTangentRho]
  unfold entropyTangentSigma entropyTangentZeroCoefficient
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [htwo]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
end TwoDegenerateGraphs
