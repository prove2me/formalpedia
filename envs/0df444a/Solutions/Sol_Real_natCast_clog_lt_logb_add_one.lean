-- Prove2me | solution 1 for Real.natCast_clog_lt_logb_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:19.665277+00:00
-- url     : https://prove2.me/submissions/4f6aaa98-c217-4032-93e3-6b3efde3b5c5

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution (b n : ℕ) : (Nat.clog b n : ℝ) < logb b n + 1 := by
  rw [← natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (div_nonneg (log_natCast_nonneg n) (log_natCast_nonneg b))
end Real
