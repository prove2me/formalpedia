-- Prove2me | solution 1 for SteklovTriangles.triangle_isoperimetric_heron
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:52:09.95635+00:00
-- url     : https://prove2.me/submissions/e2c28a11-3fdd-4bd9-a153-b3cbeea1583c

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary
import Theorems.Thm_SteklovTriangles_amgm3

set_option autoImplicit false
open SteklovTriangles
namespace SteklovTriangles
theorem _root_.solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < a + c) (h3 : c < a + b) :
    27 * ((a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c)) ≤ (a + b + c) ^ 4 := by
  have hx : 0 ≤ -a + b + c := by linarith
  have hy : 0 ≤ a - b + c := by linarith
  have hz : 0 ≤ a + b - c := by linarith
  have key := amgm3 _ _ _ hx hy hz
  have hs : (-a + b + c) + (a - b + c) + (a + b - c) = a + b + c := by ring
  rw [hs] at key
  have hL : 0 ≤ a + b + c := by linarith
  have := mul_le_mul_of_nonneg_left key hL
  nlinarith [this]
end SteklovTriangles
