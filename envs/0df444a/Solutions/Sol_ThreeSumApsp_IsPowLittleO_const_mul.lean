-- Prove2me | solution 1 for ThreeSumApsp.IsPowLittleO.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:28.815894+00:00
-- url     : https://prove2.me/submissions/d05b1529-343d-4408-a98d-23c2e096b649

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_isPowLittleO_iff
import Theorems.Thm_ThreeSumApsp_Dominated_const_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_const_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_const_mul


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
namespace IsPowLittleO
theorem _root_.solution (hf : IsPowLittleO f a) (c : ℝ) :
    IsPowLittleO (fun n => c * f n) a :=
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 hf η hη).const_mul c
end IsPowLittleO
end ThreeSumApsp
