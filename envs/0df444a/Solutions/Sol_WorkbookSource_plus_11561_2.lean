-- Prove2me | solution 2 for WorkbookSource.plus_11561
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:16:22.955593+00:00
-- url     : https://prove2.me/submissions/a46be93c-d24a-4659-bcb3-b04b9b736e96

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y ^ 2 + y * z + z ^ 2) + y / (x ^ 2 + x * z + z ^ 2) + z / (x ^ 2 + x * y + y ^ 2)) ≥ 4 / (x + y + z + 3 * (x ^ 3 + y ^ 3 + z ^ 3) / (x + y + z) ^ 2) := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : ((x / (y ^ 2 + y * z + z ^ 2) + y / (x ^ 2 + x * z + z ^ 2) + z / (x ^ 2 + x * y + y ^ 2))) - (4 / (x + y + z + 3 * (x ^ 3 + y ^ 3 + z ^ 3) / (x + y + z) ^ 2)) = (4*x^8 + 7*x^7*y + 7*x^7*z + 6*x^6*y^2 + 12*x^6*y*z + 6*x^6*z^2 + 2*x^5*y^3 + 6*x^5*y^2*z + 6*x^5*y*z^2 + 2*x^5*z^3 - 2*x^4*y^4 - 12*x^4*y^3*z - 12*x^4*y^2*z^2 - 12*x^4*y*z^3 - 2*x^4*z^4 + 2*x^3*y^5 - 12*x^3*y^4*z - 20*x^3*y^3*z^2 - 20*x^3*y^2*z^3 - 12*x^3*y*z^4 + 2*x^3*z^5 + 6*x^2*y^6 + 6*x^2*y^5*z - 12*x^2*y^4*z^2 - 20*x^2*y^3*z^3 - 12*x^2*y^2*z^4 + 6*x^2*y*z^5 + 6*x^2*z^6 + 7*x*y^7 + 12*x*y^6*z + 6*x*y^5*z^2 - 12*x*y^4*z^3 - 12*x*y^3*z^4 + 6*x*y^2*z^5 + 12*x*y*z^6 + 7*x*z^7 + 4*y^8 + 7*y^7*z + 6*y^6*z^2 + 2*y^5*z^3 - 2*y^4*z^4 + 2*y^3*z^5 + 6*y^2*z^6 + 7*y*z^7 + 4*z^8) / ((x^2 + x*y + y^2)*(x^2 + x*z + z^2)*(y^2 + y*z + z^2)*(4*x^3 + 3*x^2*y + 3*x^2*z + 3*x*y^2 + 6*x*y*z + 3*x*z^2 + 4*y^3 + 3*y^2*z + 3*y*z^2 + 4*z^3)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (4*x^8 + 7*x^7*y + 7*x^7*z + 6*x^6*y^2 + 12*x^6*y*z + 6*x^6*z^2 + 2*x^5*y^3 + 6*x^5*y^2*z + 6*x^5*y*z^2 + 2*x^5*z^3 - 2*x^4*y^4 - 12*x^4*y^3*z - 12*x^4*y^2*z^2 - 12*x^4*y*z^3 - 2*x^4*z^4 + 2*x^3*y^5 - 12*x^3*y^4*z - 20*x^3*y^3*z^2 - 20*x^3*y^2*z^3 - 12*x^3*y*z^4 + 2*x^3*z^5 + 6*x^2*y^6 + 6*x^2*y^5*z - 12*x^2*y^4*z^2 - 20*x^2*y^3*z^3 - 12*x^2*y^2*z^4 + 6*x^2*y*z^5 + 6*x^2*z^6 + 7*x*y^7 + 12*x*y^6*z + 6*x*y^5*z^2 - 12*x*y^4*z^3 - 12*x*y^3*z^4 + 6*x*y^2*z^5 + 12*x*y*z^6 + 7*x*z^7 + 4*y^8 + 7*y^7*z + 6*y^6*z^2 + 2*y^5*z^3 - 2*y^4*z^4 + 2*y^3*z^5 + 6*y^2*z^6 + 7*y*z^7 + 4*z^8) = (12/5) * (x*y*z^2) * (-y^2 + z^2)^2 + (5) * (x^2*y*z) * (-y^2 + z^2)^2 + (1) * (y^3*z) * (-x*y + z^2)^2 + (22/5) * (x*y*z^2) * (-x*y + z^2)^2 + (2) * (x^3*z) * (-x*y + z^2)^2 + (4) * (x*y^2*z) * (-x^2 + z^2)^2 + (18/5) * (x*y*z^2) * (-x^2 + y^2)^2 + (3/5) * (x^2*y^2) * (-x^2 + y^2)^2 + (6) * (x*z) * (-y^3 + z^3)^2 + (3/5) * (x*y) * (-y^3 + z^3)^2 + (3) * (x^2) * (-y^3 + z^3)^2 + (2/5) * (y^2) * (-x*y^2 + z^3)^2 + (2) * (x*y) * (-x*y^2 + z^3)^2 + (8/5) * (y*z) * (-x^2*y + z^3)^2 + (2) * (x*y) * (-x^2*y + z^3)^2 + (27/5) * (y*z) * (-x^3 + z^3)^2 + (3) * (y^2) * (-x^3 + z^3)^2 + (1) * (x*z) * (-x^3 + z^3)^2 + (3/5) * (x*y) * (-x^3 + z^3)^2 + (1) * (y*z) * (-x^3 + y*z^2)^2 + (2) * (x*z) * (-x^3 + y*z^2)^2 + (6) * (x*y) * (-x^3 + y*z^2)^2 + (2) * (y*z) * (-x^3 + y^2*z)^2 + (1) * (y*z) * (-x*z^2 + y^3)^2 + (18/5) * (x*y) * (-x*z^2 + y^3)^2 + (12/5) * (y*z) * (-x^2*z + y^3)^2 + (2) * (x*z) * (-x^2*z + y^3)^2 + (12/5) * (x*y) * (-x^2*z + y^3)^2 + (7/5) * (x^2) * (-x^2*z + y^3)^2 + (23/5) * (z^2) * (-x^3 + y^3)^2 + (18/5) * (y*z) * (-x^3 + y^3)^2 + (4) * (x*z) * (-x^3 + y^3)^2 + (2/5) * (x*y) * (-x^3 + y^3)^2 + (1) * (1) * (-y^4 + z^4)^2 + (3/5) * (1) * (-x*y^3 + z^4)^2 + (12/5) * (1) * (-x^3*y + z^4)^2 + (13/5) * (1) * (-x^4 + y*z^3)^2 + (7/5) * (1) * (-x^4 + y^3*z)^2 + (3) * (1) * (-x*z^3 + y^4)^2 := by
      ring
    rw [e]
    positivity
  · positivity
