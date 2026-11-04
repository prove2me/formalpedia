-- Prove2me | solution 1 for ThreeSumApsp.IsPowLittleO.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:43.698488+00:00
-- url     : https://prove2.me/submissions/fea874ab-102a-4b30-a290-8de2601775ab

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_isPowLittleO_iff
import Theorems.Thm_ThreeSumApsp_Dominated_add
import Theorems.Thm_ThreeSumApsp_IsBigOPow_add
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_add


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
namespace IsPowLittleO
theorem _root_.solution (hf : IsPowLittleO f a) (hg : IsPowLittleO g a) :
    IsPowLittleO (fun n => f n + g n) a :=
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 hf η hη).add (isPowLittleO_iff.1 hg η hη)
end IsPowLittleO
end ThreeSumApsp
