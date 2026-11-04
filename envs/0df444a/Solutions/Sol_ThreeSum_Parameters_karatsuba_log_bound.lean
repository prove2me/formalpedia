-- Prove2me | solution 1 for ThreeSum.Parameters.karatsuba_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:50.306345+00:00
-- url     : https://prove2.me/submissions/2205fe22-0fed-4808-9e64-3805e41c57c8

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_Parameters_power_karatsuba

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution : Real.log 3 / Real.log 2 < (8 / 5 : ℝ) := by
  have hp : (3 : ℝ) ^ 5 < 2 ^ 8 := by exact_mod_cast power_karatsuba
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 3 ^ 5) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  apply (div_lt_iff₀ log_two_pos).2
  linarith
end ThreeSum.Parameters
