-- Prove2me | solution 1 for ProximityRecipeAudit.necessary_condition_impossible
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-04T11:20:23.72131+00:00
-- url     : https://prove2.me/submissions/66a8927b-743b-4885-ac34-dddede2b1bd5

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 200000

theorem solution (A r : ℕ)
    (hA : A = 181245 ∨ A = 181235)
    (hr : 1 ≤ r) (hgate : r ^ 3 < 2130706433)
    (hrecipe : (524284 : ℝ) / ((A : ℝ) - 131071) ≤ 1 + Real.log (r : ℝ)) :
    False := by
  have hsmall : r ≤ 1286 := by
    by_contra h
    have hcube : (1287 : ℕ) ^ 3 ≤ r ^ 3 :=
      pow_le_pow_left' (show 1287 ≤ r by omega) 3
    norm_num at hcube
    omega
  have hpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hle : (r : ℝ) ≤ (2 : ℝ) ^ 11 := by
    have hcast : (r : ℝ) ≤ 1286 := by exact_mod_cast hsmall
    norm_num
    linarith
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow] at hlog
  have htwo := Real.log_two_lt_d9
  norm_num at hlog
  have hlogBound : 1 + Real.log (r : ℝ) < 9 := by linarith
  have hratio : (10 : ℝ) < 524284 / ((A : ℝ) - 131071) := by
    rcases hA with rfl | rfl <;> norm_num
  linarith

