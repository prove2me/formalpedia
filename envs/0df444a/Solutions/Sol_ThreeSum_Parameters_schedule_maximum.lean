-- Prove2me | solution 1 for ThreeSum.Parameters.schedule_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:01:43.651396+00:00
-- url     : https://prove2.me/submissions/da3ffe56-0e76-43ef-aac9-8e5d9d64a60d

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
theorem _root_.solution :
    (boxSaving - 2 * bandShift + terminalFraction) / (1 - terminalFraction)
      = (941 / 350 : ℝ) := by
  norm_num [boxSaving, bandShift, terminalFraction]
end ThreeSum.Parameters
