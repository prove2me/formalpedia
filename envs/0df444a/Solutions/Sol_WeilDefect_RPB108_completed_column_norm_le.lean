-- Prove2me | solution 1 for WeilDefect.RPB108.completed_column_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:18:04.645532+00:00
-- url     : https://prove2.me/submissions/49b45ae0-5433-4e13-a089-496a7afab4b8

import Theorems.Thm_WeilDefect_RPB108_completed_mass_bound_of_squared_certificate
import Mathlib
open scoped BigOperators
set_option autoImplicit false
open WeilDefect.RPB108
theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x source : E) (m q k B : ℝ)
    (hk : 0 < k) (hT : ‖T‖ ≤ 1/k) (hx : ‖x‖ ≤ m)
    (hsource : ‖source‖^2 ≤ q) (hm : m ≤ B)
    (hq : q ≤ (k*(B-m))^2) : ‖x-T source‖ ≤ B := by
  have hs : ‖source‖ ≤ Real.sqrt q := Real.le_sqrt_of_sq_le hsource
  have ht : ‖T source‖ ≤ Real.sqrt q/k := by
    calc
      ‖T source‖ ≤ ‖T‖*‖source‖ := T.le_opNorm source
      _ ≤ (1/k)*‖source‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
      _ ≤ (1/k)*Real.sqrt q := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = Real.sqrt q/k := by ring
  calc
    ‖x-T source‖ ≤ ‖x‖+‖T source‖ := norm_sub_le _ _
    _ ≤ m+Real.sqrt q/k := add_le_add hx ht
    _ ≤ B := completed_mass_bound_of_squared_certificate m q k B hk hm hq
