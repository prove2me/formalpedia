-- Prove2me | solution 1 for Real.log_two_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:19.40314+00:00
-- url     : https://prove2.me/submissions/781a18df-2a93-4582-9c3a-75ffeaa2e29d

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution : log 2 < 1 :=
  log_two_lt_d9.trans (by norm_num)
end Real
