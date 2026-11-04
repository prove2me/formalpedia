-- Prove2me | solution 1 for ThreeSumApsp.isPowPolylog_log_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:02.337027+00:00
-- url     : https://prove2.me/submissions/29895b60-57e2-4f8e-99fe-c0a04fab9b32

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_add
import Theorems.Thm_ThreeSumApsp_IsBigOPow_const_mul
import Theorems.Thm_ThreeSumApsp_isPowPolylog_log
import Theorems.Thm_ThreeSumApsp_isPowPolylog_const
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_add
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_const_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_congr
import Theorems.Thm_ThreeSumApsp_Dominated_add
import Theorems.Thm_ThreeSumApsp_Dominated_congr
import Theorems.Thm_ThreeSumApsp_Dominated_const_mul


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
theorem _root_.solution (c κ : ℝ) :
    IsPowPolylog (fun n : ℕ => Real.log (c * (n : ℝ) ^ κ)) 0 := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa only [zero_mul, Real.log_zero] using isPowPolylog_const 0
  · refine ((isPowPolylog_const (Real.log c)).add (isPowPolylog_log.const_mul κ)).congr ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [Real.log_mul hc (Real.rpow_pos_of_pos hpos κ).ne', Real.log_rpow hpos]
end ThreeSumApsp
