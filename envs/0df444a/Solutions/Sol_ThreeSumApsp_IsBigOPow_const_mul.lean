-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:10.601544+00:00
-- url     : https://prove2.me/submissions/b526be61-c234-4968-b2da-f5c2f68893dd

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow
namespace ThreeSumApsp.IsBigOPow
theorem _root_.solution (hf : IsBigOPow f a) (c : ℝ) : IsBigOPow (fun n => c * f n) a :=
  IsBigO.const_mul_left hf c
end ThreeSumApsp.IsBigOPow
