-- Prove2me | solution 1 for ThreeSumApsp.isBigOPow_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:11.899242+00:00
-- url     : https://prove2.me/submissions/8acd2e4e-1881-486e-a594-d891744ff92f

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_isBigOPow_rpow

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
theorem _root_.solution : IsBigOPow (fun n : ℕ => (n : ℝ)) 1 := by
  simpa only [Real.rpow_one] using isBigOPow_rpow 1
end ThreeSumApsp
