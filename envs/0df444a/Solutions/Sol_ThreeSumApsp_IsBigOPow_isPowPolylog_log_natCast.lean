-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.isPowPolylog_log_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:31.989199+00:00
-- url     : https://prove2.me/submissions/6cef4734-071a-4224-8090-6a26aa924716

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left_of_nonneg
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_const_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_eventually_abs_le
import Theorems.Thm_ThreeSumApsp_isPowPolylog_log
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono_left_of_nonneg
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_const_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_eventually_abs_le
import Theorems.Thm_ThreeSumApsp_Dominated_const_mul


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
namespace IsBigOPow
theorem _root_.solution {size : ℕ → ℕ} {μ : ℝ}
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) :
    IsPowPolylog (fun n => Real.log (size n)) 0 := by
  refine (isPowPolylog_log.const_mul (max μ 0 + 1)).mono_left_of_nonneg
    (Eventually.of_forall fun n => Real.log_natCast_nonneg _) ?_
  filter_upwards [(hsize.mono (le_max_left μ 0)).eventually_abs_le (lt_add_one _),
    eventually_gt_atTop 0] with n hle hn
  obtain hzero | hpos := (size n).eq_zero_or_pos
  · rw [hzero, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (add_nonneg (le_max_right μ 0) zero_le_one) (Real.log_natCast_nonneg n)
  · rw [abs_of_nonneg (Nat.cast_nonneg _)] at hle
    rw [← Real.log_rpow (Nat.cast_pos.2 hn)]
    exact Real.log_le_log (Nat.cast_pos.2 hpos) hle
end IsBigOPow
end ThreeSumApsp
