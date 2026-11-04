-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:14:20.910207+00:00
-- url     : https://prove2.me/submissions/2e04b7aa-3c46-47b7-8ae7-3fdc084909f1

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_isBigO_rpow_rpow_of_le


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow
namespace ThreeSumApsp.IsBigOPow
theorem _root_.solution (hf : IsBigOPow f a) (hab : a ≤ b) : IsBigOPow f b :=
  hf.trans (isBigO_rpow_rpow_of_le hab)
end ThreeSumApsp.IsBigOPow
