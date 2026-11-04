-- Prove2me | solution 1 for ThreeSumApsp.isLittleO_rpow_mul_log_pow_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:30.947775+00:00
-- url     : https://prove2.me/submissions/2662f52a-5392-42e1-8675-84a57981ddba

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Theorems.Thm_ThreeSumApsp_rpow_mul_rpow_eventuallyEq
import Theorems.Thm_ThreeSumApsp_isLittleO_log_pow_rpow

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a) atTop).mul_isLittleO
    (isLittleO_log_pow_rpow (sub_pos.2 hab) e)
  refine h.congr' EventuallyEq.rfl ?_
  simpa only [add_sub_cancel] using rpow_mul_rpow_eventuallyEq a (b - a)
end ThreeSumApsp
