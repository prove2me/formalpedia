-- Prove2me | solution 1 for ThreeSum.Parameters.recursive_exponent_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:01:47.279216+00:00
-- url     : https://prove2.me/submissions/0b6b28ad-f313-4739-81e2-fc89646b84a1

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
    2 - epsilon *
      (1 / 2 - bandShift - kappaCap - entropyRatio * (1 + boxSaving - 2 * bandShift))
      = certificateExponent := by
  norm_num [epsilon, bandShift, kappaCap, entropyRatio, boxSaving, certificateExponent]
end ThreeSum.Parameters
