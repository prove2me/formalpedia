-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:15.247499+00:00
-- url     : https://prove2.me/submissions/8d4c5018-303c-4b2b-a6a5-8b8aa6b5b47e

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_add


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow
namespace ThreeSumApsp.IsBigOPow
theorem _root_.solution (hf : IsBigOPow f a) (hg : IsBigOPow g a) :
    IsBigOPow (fun n => f n + g n) a :=
  IsBigO.add hf hg
end ThreeSumApsp.IsBigOPow
