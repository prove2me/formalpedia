-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:26:07.826586+00:00
-- url     : https://prove2.me/submissions/0826fc43-dc65-4350-b4b0-deb1db8ee7aa

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (r : ℕ) (hr : 1 ≤ r) : (r : ℝ) * (Real.exp (2 / (3 * r)) - 1) < 1 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : 0 < 2 / (3 * (r : ℝ)) := by positivity
  set x : ℝ := 2 / (3 * (r : ℝ)) with hx
  have hxr : (r : ℝ) * x = 2 / 3 := by rw [hx]; field_simp
  have hx1 : x ≤ 2 / 3 := by nlinarith
  have hb := Real.exp_bound (x := x) (by rw [abs_of_pos hx0]; linarith) (n := 4) (by norm_num)
  rw [abs_of_pos hx0] at hb
  have hup := (abs_le.mp hb).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hup
  norm_num at hup
  have hmain : Real.exp x - 1 < 3 / 2 * x := by
    nlinarith [pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4, mul_le_mul_of_nonneg_left hx1 (le_of_lt (pow_pos hx0 3))]
  have hr0 : (0 : ℝ) < r := by linarith
  calc (r : ℝ) * (Real.exp x - 1) < r * (3 / 2 * x) := mul_lt_mul_of_pos_left hmain hr0
    _ = 1 := by rw [show (r : ℝ) * (3 / 2 * x) = 3 / 2 * (r * x) by ring, hxr]; norm_num
end ReciprocityTheory.MultiplicativeHeights
