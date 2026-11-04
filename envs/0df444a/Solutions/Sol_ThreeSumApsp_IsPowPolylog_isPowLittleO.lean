-- Prove2me | solution 1 for ThreeSumApsp.IsPowPolylog.isPowLittleO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:05.316217+00:00
-- url     : https://prove2.me/submissions/76877d01-edb4-4547-8ab6-325a0926252e

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_isPowLittleO_iff
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_isBigOPow
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_isBigOPow


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
namespace IsPowPolylog
theorem _root_.solution (h : IsPowPolylog f a) : IsPowLittleO f a :=
  isPowLittleO_iff.2 fun _ hη => h.isBigOPow (by linarith)
end IsPowPolylog
end ThreeSumApsp
