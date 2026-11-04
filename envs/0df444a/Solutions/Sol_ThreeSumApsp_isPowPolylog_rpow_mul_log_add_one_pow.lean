-- Prove2me | solution 1 for ThreeSumApsp.isPowPolylog_rpow_mul_log_add_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:00.978341+00:00
-- url     : https://prove2.me/submissions/bb3910f2-8160-4376-b375-6b241500fff3

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_add
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_pow
import Theorems.Thm_ThreeSumApsp_isPowPolylog_rpow__8aeb32
import Theorems.Thm_ThreeSumApsp_isPowPolylog_log
import Theorems.Thm_ThreeSumApsp_isPowPolylog_const
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_add
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_pow
import Theorems.Thm_ThreeSumApsp_Dominated_add
import Theorems.Thm_ThreeSumApsp_Dominated_mul
import Theorems.Thm_ThreeSumApsp_Dominated_pow


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
theorem _root_.solution (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * (Real.log n + 1) ^ e) a := by
  have h := (isPowPolylog_rpow a).mul ((isPowPolylog_log.add (isPowPolylog_const 1)).pow e)
  rwa [zero_mul, add_zero] at h
end ThreeSumApsp
