-- Prove2me | solution 1 for SteklovTriangles.amgm3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:51:05.73245+00:00
-- url     : https://prove2.me/submissions/68055863-5d0e-42ac-bb10-d42763f56cb8

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary

set_option autoImplicit false
open SteklovTriangles
namespace SteklovTriangles
theorem _root_.solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
    mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hx hz,
    mul_nonneg (mul_nonneg hx hy) hz, sq_nonneg (x + y - 2 * z),
    mul_nonneg hz (sq_nonneg (x - y)), mul_nonneg hx (sq_nonneg (y - z)),
    mul_nonneg hy (sq_nonneg (x - z))]
end SteklovTriangles
