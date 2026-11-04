-- Prove2me | solution 1 for ThreeSumApsp.eventually_mul_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:25.940109+00:00
-- url     : https://prove2.me/submissions/faf62c77-acf4-4e3d-a11f-fe46c2a04e6c

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Theorems.Thm_ThreeSumApsp_eventually_mul_rpow_mul_log_pow_le

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  simpa only [pow_zero, mul_one] using eventually_mul_rpow_mul_log_pow_le C hab 0
end ThreeSumApsp
