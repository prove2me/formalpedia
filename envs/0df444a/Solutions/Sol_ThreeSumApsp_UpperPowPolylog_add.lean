-- Prove2me | solution 1 for ThreeSumApsp.UpperPowPolylog.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:07.892331+00:00
-- url     : https://prove2.me/submissions/18006257-944a-42a1-81e6-692e32407c23

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_UpperBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_upperPowPolylog
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono_left
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_exists_isPowPolylog
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_Dominated_add
import Theorems.Thm_ThreeSumApsp_Dominated_mono_left
import Theorems.Thm_ThreeSumApsp_IsBigOPow_add
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_add
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_add
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono_left


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog
namespace ThreeSumApsp.UpperPowPolylog
theorem _root_.solution (hf : UpperPowPolylog f a) (hg : UpperPowPolylog g a) :
    UpperPowPolylog (fun n => f n + g n) a := by
  obtain ⟨F, -, hF, hfF⟩ := hf.exists_isPowPolylog
  obtain ⟨G, -, hG, hgG⟩ := hg.exists_isPowPolylog
  exact (hF.add hG).upperPowPolylog.mono_left
    ((hfF.and hgG).mono fun n hn => add_le_add hn.1 hn.2)
end ThreeSumApsp.UpperPowPolylog
