-- Prove2me | solution 1 for ThreeSum.Parameters.recursive_saving_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:01:46.190652+00:00
-- url     : https://prove2.me/submissions/62574a21-fe23-4b41-9091-e891813fe274

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
    1 / 2 - bandShift - kappaCap - entropyRatio * (1 + boxSaving - 2 * bandShift)
      = (190893 / 1000000 : ℝ) := by
  norm_num [bandShift, kappaCap, entropyRatio, boxSaving]
end ThreeSum.Parameters
