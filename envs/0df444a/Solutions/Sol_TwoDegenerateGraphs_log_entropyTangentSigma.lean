-- Prove2me | solution 1 for TwoDegenerateGraphs.log_entropyTangentSigma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/3fbf82bd-1660-4782-8627-0447381af0cf

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Real.log entropyTangentSigma =
      (3 / 2 : ℝ) * Real.log 2 - Real.log 3 := by
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  unfold entropyTangentSigma
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), hlogfour]
  ring
end TwoDegenerateGraphs
