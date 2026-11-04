-- Prove2me | solution 1 for ThreeSumApsp.UpperPowLittleO.upperBigOPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:13.668716+00:00
-- url     : https://prove2.me/submissions/fb5f3c62-fd37-4271-9b60-49147a09883b

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_IsBigOPow_upperBigOPow
import Theorems.Thm_ThreeSumApsp_UpperBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono_left
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_upperBigOPow
import Theorems.Thm_ThreeSumApsp_UpperPowLittleO_mono_left
import Theorems.Thm_ThreeSumApsp_UpperPowLittleO_exists_isPowLittleO
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
open ThreeSumApsp.UpperPowLittleO
namespace ThreeSumApsp.UpperPowLittleO
theorem _root_.solution (h : UpperPowLittleO f a) (hab : a < b) : UpperBigOPow f b := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowLittleO
  exact (hg.isBigOPow hab).upperBigOPow.mono_left hfg
end ThreeSumApsp.UpperPowLittleO
