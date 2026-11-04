-- Prove2me | solution 1 for ThreeSumApsp.IsPowPolylog.mul_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:52.863586+00:00
-- url     : https://prove2.me/submissions/b0ad6e05-3897-41ee-bef3-96451b5fb183

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_const_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_const_mul
import Theorems.Thm_ThreeSumApsp_Dominated_const_mul


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsPowPolylog
namespace ThreeSumApsp.IsPowPolylog
theorem _root_.solution (hf : IsPowPolylog f a) (c : ℝ) : IsPowPolylog (fun n => f n * c) a := by
  simpa only [mul_comm] using hf.const_mul c
end ThreeSumApsp.IsPowPolylog
