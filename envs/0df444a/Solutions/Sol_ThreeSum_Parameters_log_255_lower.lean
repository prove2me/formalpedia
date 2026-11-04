-- Prove2me | solution 1 for ThreeSum.Parameters.log_255_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:23.355826+00:00
-- url     : https://prove2.me/submissions/4834ef9d-e3a4-4506-af53-f9335b3ce8a6

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_power_255

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution : (799 / 100 : ℝ) * Real.log 2 < Real.log 255 := by
  have hp : (2 : ℝ) ^ 799 < 255 ^ 100 := by exact_mod_cast power_255
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ 799) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith
end ThreeSum.Parameters
