-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:24.529197+00:00
-- url     : https://prove2.me/submissions/36c2d788-c59d-4d60-8aa1-9667466c442e

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_rpow__dbdce0

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow
namespace ThreeSumApsp.IsBigOPow
theorem _root_.solution (hf : IsBigOPow f a) (k : ℕ) : IsBigOPow (fun n => f n ^ k) (a * k) := by
  simpa only [Real.rpow_natCast] using hf.rpow k.cast_nonneg
end ThreeSumApsp.IsBigOPow
