-- Prove2me | solution 1 for Real.log_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:20.656019+00:00
-- url     : https://prove2.me/submissions/0e4ebe3b-8dc7-46a1-81ab-3d0d26214b63

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution : log 9 = 2 * log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]
end Real
