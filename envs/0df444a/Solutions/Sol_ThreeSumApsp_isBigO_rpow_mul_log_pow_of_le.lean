-- Prove2me | solution 1 for ThreeSumApsp.isBigO_rpow_mul_log_pow_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:29.753936+00:00
-- url     : https://prove2.me/submissions/e85569c8-5766-4dfb-84d9-bca5a012ce9c

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Theorems.Thm_ThreeSumApsp_isBigO_rpow_rpow_of_le
import Theorems.Thm_ThreeSumApsp_isBigO_log_pow_log_pow_of_le

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {a b : ℝ} {e e' : ℕ} (hab : a ≤ b) (he : e ≤ e') :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ b * Real.log n ^ e' :=
  (isBigO_rpow_rpow_of_le hab).mul (isBigO_log_pow_log_pow_of_le he)
end ThreeSumApsp
