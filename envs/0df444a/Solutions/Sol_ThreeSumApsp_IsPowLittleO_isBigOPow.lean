-- Prove2me | solution 1 for ThreeSumApsp.IsPowLittleO.isBigOPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:43.342722+00:00
-- url     : https://prove2.me/submissions/f450a8b8-c6aa-4ed5-8756-4b3a3d597b57

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
namespace IsPowLittleO
theorem _root_.solution (h : IsPowLittleO f a) (hab : a < b) : IsBigOPow f b :=
  (isPowLittleO_iff.1 h (b - a) (sub_pos.2 hab)).mono (by linarith)
end IsPowLittleO
end ThreeSumApsp
