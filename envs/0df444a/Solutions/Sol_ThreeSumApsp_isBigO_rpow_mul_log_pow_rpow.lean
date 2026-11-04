-- Prove2me | solution 1 for ThreeSumApsp.isBigO_rpow_mul_log_pow_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:18.736966+00:00
-- url     : https://prove2.me/submissions/db8f243d-7ed7-4dc2-ad69-34f7ff4da2f4

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Theorems.Thm_ThreeSumApsp_isLittleO_rpow_mul_log_pow_rpow

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop] fun n : ℕ => (n : ℝ) ^ b :=
  (isLittleO_rpow_mul_log_pow_rpow hab e).isBigO
end ThreeSumApsp
