-- Prove2me | solution 1 for ThreeSumApsp.UpperPowPolylog.upperBigOPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:45.394426+00:00
-- url     : https://prove2.me/submissions/a97f6340-55ff-42d1-ad3e-2e71a4f958ba

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_IsBigOPow_upperBigOPow
import Theorems.Thm_ThreeSumApsp_UpperBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono_left
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_exists_isPowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_mono_left
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_isBigOPow
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_isBigOPow
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono_left


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog
namespace ThreeSumApsp.UpperPowPolylog
theorem _root_.solution (h : UpperPowPolylog f a) (hab : a < b) : UpperBigOPow f b := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowPolylog
  exact (hg.isBigOPow hab).upperBigOPow.mono_left hfg
end ThreeSumApsp.UpperPowPolylog
