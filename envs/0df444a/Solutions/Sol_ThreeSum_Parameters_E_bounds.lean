-- Prove2me | solution 1 for ThreeSum.Parameters.E_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:22.533102+00:00
-- url     : https://prove2.me/submissions/c79c320f-c13a-4658-95c0-5b1343ece125

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_log_two_lower
import Theorems.Thm_ThreeSum_Parameters_E_formula

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution : (4 : ℝ) < E ∧ E < 19 / 4 := by
  have hpos : 0 < Real.log (256 / 255 : ℝ) := Real.log_pos (by norm_num)
  have hlt : Real.log (256 / 255 : ℝ) < 1 / 255 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 256 / 255)
      (by norm_num : (256 / 255 : ℝ) ≠ 1)
    norm_num at h
    exact h
  rw [E_formula]
  constructor
  · have : 0 < 255 * Real.log (256 / 255 : ℝ) / (2 * Real.log 2) := by positivity
    linarith
  · have : 255 * Real.log (256 / 255 : ℝ) / (2 * Real.log 2) < 3 / 4 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
      linarith [log_two_lower]
    linarith
end ThreeSum.Parameters
