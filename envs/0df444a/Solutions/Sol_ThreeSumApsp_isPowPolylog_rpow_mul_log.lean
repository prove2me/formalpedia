-- Prove2me | solution 1 for ThreeSumApsp.isPowPolylog_rpow_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:50.162167+00:00
-- url     : https://prove2.me/submissions/33827a98-d7fe-47ad-b69d-b2f22a345629

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_isPowPolylog_rpow_mul_log_pow

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
theorem _root_.solution (a : ℝ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * Real.log n) a := by
  simpa only [pow_one] using isPowPolylog_rpow_mul_log_pow a 1
end ThreeSumApsp
