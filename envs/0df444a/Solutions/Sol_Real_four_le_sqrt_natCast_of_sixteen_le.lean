-- Prove2me | solution 1 for Real.four_le_sqrt_natCast_of_sixteen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:48.94099+00:00
-- url     : https://prove2.me/submissions/bbbfec5f-33bb-4eb7-ab0d-3e4418cde8c3

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution {D : ℕ} (hD : 16 ≤ D) : 4 ≤ √(D : ℝ) :=
  le_sqrt_of_sq_le (by norm_num; exact_mod_cast hD)
end Real
