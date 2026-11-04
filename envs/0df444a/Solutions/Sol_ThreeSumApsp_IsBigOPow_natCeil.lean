-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.natCeil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:20.830057+00:00
-- url     : https://prove2.me/submissions/d458fc13-43c2-42b5-8481-c50cb7a2c1b1

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_isBigOPow_const
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left_of_nonneg
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_add
import Theorems.Thm_ThreeSumApsp_IsBigOPow_abs
import Theorems.Thm_ThreeSumApsp_Dominated_add
import Theorems.Thm_ThreeSumApsp_Dominated_trans


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
namespace IsBigOPow
theorem _root_.solution (hf : IsBigOPow f a) (ha : 0 ≤ a) :
    IsBigOPow (fun n => (⌈f n⌉₊ : ℝ)) a := by
  refine (hf.abs.add ((isBigOPow_const 1).mono ha)).mono_left_of_nonneg
    (Eventually.of_forall fun n => Nat.cast_nonneg _) (Eventually.of_forall fun n => ?_)
  obtain hneg | hpos := le_or_gt (f n) 0
  · rw [Nat.ceil_eq_zero.2 hneg, Nat.cast_zero]
    positivity
  · exact (Nat.ceil_lt_add_one hpos.le).le.trans (add_le_add_left (le_abs_self _) 1)
end IsBigOPow
end ThreeSumApsp
