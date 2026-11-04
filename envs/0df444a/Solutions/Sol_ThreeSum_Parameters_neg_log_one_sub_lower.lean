-- Prove2me | solution 1 for ThreeSum.Parameters.neg_log_one_sub_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:41.708201+00:00
-- url     : https://prove2.me/submissions/f9da1c21-afe7-4860-a4a8-f5b4374a6430

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
theorem _root_.solution {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t + t ^ 2 / 2 ≤ -Real.log (1 - t) := by
  have habs : |t| < 1 := by rwa [abs_of_nonneg ht0]
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h := sum_le_hasSum (Finset.range 2)
    (fun n _ => div_nonneg (pow_nonneg ht0 _) (by positivity)) hs
  norm_num [Finset.sum_range_succ] at h
  exact h
end ThreeSum.Parameters
