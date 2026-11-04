-- Prove2me | solution 1 for Real.one_le_log_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:21.880988+00:00
-- url     : https://prove2.me/submissions/728eafce-5ef2-4b67-869e-dba514e5a746

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Theorems.Thm_Real_one_half_lt_log_two
import Theorems.Thm_Real_log_four

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution : 1 ≤ log 4 := by
  linarith [log_four, one_half_lt_log_two]
end Real
