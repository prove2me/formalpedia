-- Prove2me | solution 1 for ThreeSumApsp.IsPowPolylog.eventually_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:33.992999+00:00
-- url     : https://prove2.me/submissions/1397bed1-3c59-4f63-94ab-dbc21e5176ec

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_eventually_abs_le
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_isBigOPow

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsPowPolylog
namespace ThreeSumApsp.IsPowPolylog
theorem _root_.solution (hf : IsPowPolylog f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b :=
  (hf.isBigOPow (left_lt_add_div_two.2 hab)).eventually_abs_le (add_div_two_lt_right.2 hab)
end ThreeSumApsp.IsPowPolylog
