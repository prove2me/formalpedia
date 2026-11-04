-- Prove2me | solution 1 for Real.log_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:06.119199+00:00
-- url     : https://prove2.me/submissions/358b5a11-495a-42dc-b042-a83d921b3404

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]
end Real
