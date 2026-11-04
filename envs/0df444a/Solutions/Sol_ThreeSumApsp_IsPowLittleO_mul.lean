-- Prove2me | solution 1 for ThreeSumApsp.IsPowLittleO.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:07.490887+00:00
-- url     : https://prove2.me/submissions/d1d62e3d-1782-4a5a-864e-2b82004bca00

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_isPowLittleO_iff
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_Dominated_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mul


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
namespace IsPowLittleO
theorem _root_.solution (hf : IsPowLittleO f a) (hg : IsPowLittleO g b) :
    IsPowLittleO (fun n => f n * g n) (a + b) :=
  isPowLittleO_iff.2 fun η hη => ((isPowLittleO_iff.1 hf _ (half_pos hη)).mul
    (isPowLittleO_iff.1 hg _ (half_pos hη))).mono (by linarith)
end IsPowLittleO
end ThreeSumApsp
