-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.isPowLittleO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:03.980502+00:00
-- url     : https://prove2.me/submissions/da874b45-2d22-4ab3-91fe-ebefc1808ac0

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_isPowLittleO_iff
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
namespace IsBigOPow
theorem _root_.solution (h : IsBigOPow f a) : IsPowLittleO f a :=
  isPowLittleO_iff.2 fun _ hη => h.mono (by linarith)
end IsBigOPow
end ThreeSumApsp
