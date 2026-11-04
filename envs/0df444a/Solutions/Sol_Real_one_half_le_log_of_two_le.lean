-- Prove2me | solution 1 for Real.one_half_le_log_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:46.277802+00:00
-- url     : https://prove2.me/submissions/e91719bf-a868-4c5e-be31-2e784c5d5cc4

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Theorems.Thm_Real_one_half_lt_log_two

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution {x : ℝ} (hx : 2 ≤ x) : 1 / 2 ≤ log x :=
  one_half_lt_log_two.le.trans (log_le_log two_pos hx)
end Real
