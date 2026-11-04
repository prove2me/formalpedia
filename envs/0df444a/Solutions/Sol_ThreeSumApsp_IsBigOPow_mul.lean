-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:18:01.649086+00:00
-- url     : https://prove2.me/submissions/31b618b7-6389-4186-80f4-f3db5c1721b0

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_mul
import Theorems.Thm_ThreeSumApsp_rpow_mul_rpow_eventuallyEq


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow
namespace ThreeSumApsp.IsBigOPow
theorem _root_.solution (hf : IsBigOPow f a) (hg : IsBigOPow g b) :
    IsBigOPow (fun n => f n * g n) (a + b) :=
  (IsBigO.mul hf hg).congr' EventuallyEq.rfl (rpow_mul_rpow_eventuallyEq a b)
end ThreeSumApsp.IsBigOPow
