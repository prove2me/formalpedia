-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:16.347929+00:00
-- url     : https://prove2.me/submissions/6b056cef-0047-4846-a6c7-b7293e245ea0

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
theorem _root_.solution (hf : IsBigOPow f a) {r : ℝ} (hr : 0 ≤ r) :
    IsBigOPow (fun n => f n ^ r) (a * r) := by
  have h := IsBigO.rpow hr (Eventually.of_forall fun n : ℕ => Real.rpow_nonneg n.cast_nonneg a) hf
  exact h.congr_right fun n => (Real.rpow_mul n.cast_nonneg a r).symm
end ThreeSumApsp.IsBigOPow
