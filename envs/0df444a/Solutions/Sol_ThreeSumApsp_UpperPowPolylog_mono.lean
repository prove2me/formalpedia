-- Prove2me | solution 1 for ThreeSumApsp.UpperPowPolylog.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:30.583282+00:00
-- url     : https://prove2.me/submissions/664b4df5-f4f3-4ebe-9e0d-64693cf24bb1

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_UpperBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_upperPowPolylog
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono_left
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_exists_isPowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_mono_left
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono_left


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog
namespace ThreeSumApsp.UpperPowPolylog
theorem _root_.solution (h : UpperPowPolylog f a) (hab : a ≤ b) : UpperPowPolylog f b := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowPolylog
  exact (hg.mono hab).upperPowPolylog.mono_left hfg
end ThreeSumApsp.UpperPowPolylog
