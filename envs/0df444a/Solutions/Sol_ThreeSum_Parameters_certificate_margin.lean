-- Prove2me | solution 1 for ThreeSum.Parameters.certificate_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:51.521926+00:00
-- url     : https://prove2.me/submissions/7bbe5faa-e077-4078-bd64-07960e0d87e8

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
theorem _root_.solution : targetExponent - certificateExponent = (893 / 5000000 : ℝ) := by
  norm_num [targetExponent, certificateExponent]
end ThreeSum.Parameters
