-- Prove2me | solution 1 for ThreeSum.Parameters.entropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:24.523684+00:00
-- url     : https://prove2.me/submissions/4fcd5dd0-403c-42cd-9f21-2e1831606e83

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
theorem _root_.solution (t : ℝ) :
    entropy t = (-t * Real.log t - (1 - t) * Real.log (1 - t)) / Real.log 2 := by
  simp only [entropy, Real.binEntropy, Real.log_inv]
  ring
end ThreeSum.Parameters
