-- Prove2me | solution 1 for Sendov.sqrt_le_tangent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:14.880239+00:00
-- url     : https://prove2.me/submissions/31c52621-46d6-4133-853d-f0b25d9643b8

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_OddBound

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α q w : ℝ}
namespace Sendov
theorem _root_.solution (hq : 0 ≤ q) (hw : 0 < w) : Real.sqrt q ≤ q / (2 * w) + w / 2 := by
  have hrw : q / (2 * w) + w / 2 = (q + w ^ 2) / (2 * w) := by field_simp
  rw [hrw, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt q - w), Real.sq_sqrt hq]
end Sendov
