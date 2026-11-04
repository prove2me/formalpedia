-- Prove2me | solution 1 for ThreeSumApsp.IsPowLittleO.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:11.464757+00:00
-- url     : https://prove2.me/submissions/5a2490a8-eaa7-43b6-8a8d-b766c8fa09b7

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_isPowLittleO_iff
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
namespace IsPowLittleO
theorem _root_.solution (h : IsPowLittleO f a) (hab : a ≤ b) : IsPowLittleO f b :=
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 h η hη).mono (by linarith)
end IsPowLittleO
end ThreeSumApsp
