-- Prove2me | solution 1 for ThreeSum.Parameters.tangent_right_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:38.241439+00:00
-- url     : https://prove2.me/submissions/c76f0105-e99d-41de-9fd7-065b03cfdbc1

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
    entropyRatio * (1 + phi tangentPoint + (1 / 2 - tangentPoint) * phiDeriv tangentPoint)
      = (4418702061 / 3125000000 : ℝ) := by
  norm_num [entropyRatio, tangentPoint, phi, phiDeriv]
end ThreeSum.Parameters
