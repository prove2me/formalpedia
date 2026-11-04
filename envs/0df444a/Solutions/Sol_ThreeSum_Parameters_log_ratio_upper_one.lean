-- Prove2me | solution 1 for ThreeSum.Parameters.log_ratio_upper_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:32.801454+00:00
-- url     : https://prove2.me/submissions/93d76896-fb5d-48b4-8fc2-958e0cd7be07

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {x : ℝ} (hx : |x| < 1) :
    Real.log ((1 + x) / (1 - x)) ≤ 2 * x + 2 * |x| ^ 3 / (1 - x ^ 2) := by
  have h := (abs_le.mp (Real.sum_range_sub_log_div_le hx 1)).2
  norm_num [Finset.sum_range_succ] at h
  rw [show 2 * |x| ^ 3 / (1 - x ^ 2) = 2 * (|x| ^ 3 / (1 - x ^ 2)) by ring]
  linarith
end ThreeSum.Parameters
