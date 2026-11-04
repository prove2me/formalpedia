-- Prove2me | solution 1 for Real.one_le_log_natCast_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:40.826796+00:00
-- url     : https://prove2.me/submissions/9cc405ac-eba0-433d-b502-acd52b65f3b4

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Theorems.Thm_Real_one_le_log_of_three_le

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution {n : ℕ} (hn : 3 ≤ n) : 1 ≤ log n :=
  one_le_log_of_three_le (by exact_mod_cast hn)
end Real
