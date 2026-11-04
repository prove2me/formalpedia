-- Prove2me | solution 1 for Real.one_le_log_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:07.371872+00:00
-- url     : https://prove2.me/submissions/043c64ad-8abe-4ed1-abb4-4594e49b900c

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution {x : ℝ} (hx : 3 ≤ x) : 1 ≤ log x :=
  (le_log_iff_exp_le (by linarith)).2 (exp_one_lt_three.le.trans hx)
end Real
