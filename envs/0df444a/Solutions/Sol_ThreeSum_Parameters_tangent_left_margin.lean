-- Prove2me | solution 1 for ThreeSum.Parameters.tangent_left_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:17.900023+00:00
-- url     : https://prove2.me/submissions/3f8039f1-1b70-48ee-b194-12aac6c99bed

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_tangent_left_polynomial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution :
    (27 / 100 : ℝ) < entropyRatio *
      (1 + phi tangentPoint - tangentPoint * phiDeriv tangentPoint) := by
  rw [tangent_left_polynomial]
  norm_num
end ThreeSum.Parameters
