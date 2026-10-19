-- Prove2me | solution 1 for TwoDegenerateGraphs.entropyTangentLog_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/f4815895-d0fb-4746-b33e-b8939a6e1967

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_log_entropyTangentSigma
import Theorems.Thm_TwoDegenerateGraphs_log_entropyTangentRho

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (q : ℝ) :
    ((1 - q) ^ 2 + q ^ 2) * Real.log entropyTangentSigma +
        2 * q * (1 - q) * Real.log entropyTangentRho =
      Real.log 2 - (3 / 4 : ℝ) * Real.log 3 +
        (2 * q - 1) ^ 2 / 4 * Real.log ((4 : ℝ) / 3) := by
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [log_entropyTangentSigma, log_entropyTangentRho,
    Real.log_div (by positivity) (by positivity), hlogfour]
  ring
end TwoDegenerateGraphs
