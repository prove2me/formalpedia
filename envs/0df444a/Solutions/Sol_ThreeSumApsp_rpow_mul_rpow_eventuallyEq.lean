-- Prove2me | solution 1 for ThreeSumApsp.rpow_mul_rpow_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:02.674298+00:00
-- url     : https://prove2.me/submissions/5afdd936-bda0-499d-96b5-cbfb40de4e67

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution (a b : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ b) =ᶠ[atTop] fun n : ℕ => (n : ℝ) ^ (a + b) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_add (Nat.cast_pos.2 hn)]
end ThreeSumApsp
