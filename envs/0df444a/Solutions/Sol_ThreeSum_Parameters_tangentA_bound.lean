-- Prove2me | solution 1 for ThreeSum.Parameters.tangentA_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:33.819384+00:00
-- url     : https://prove2.me/submissions/464bbd31-7ab8-491e-80dc-23b6c852dd63

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
import Theorems.Thm_ThreeSum_Parameters_power_tangent_left

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution : tangentA < (27 / 100 : ℝ) := by
  have hp : (100 : ℝ) ^ 100 < 2 ^ 27 * 83 ^ 100 := by
    exact_mod_cast power_tangent_left
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 100 ^ 100) hp
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 27 ≠ 0)
    (by positivity : (83 : ℝ) ^ 100 ≠ 0)] at h
  simp only [Real.log_pow] at h
  norm_num at h
  apply (div_lt_iff₀ log_two_pos).2
  linarith
end ThreeSum.Parameters
