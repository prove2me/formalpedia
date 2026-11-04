-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.eventually_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:59.376542+00:00
-- url     : https://prove2.me/submissions/897147a9-94ad-4b48-a72f-11d1d4afbb2f

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_eventually_mul_rpow_le


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow
namespace ThreeSumApsp.IsBigOPow
theorem _root_.solution (hf : IsBigOPow f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by
  obtain ⟨C, hC⟩ := IsBigO.bound hf
  filter_upwards [hC, eventually_mul_rpow_le C hab] with n hn hCn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)] at hn
  exact hn.trans hCn
end ThreeSumApsp.IsBigOPow
