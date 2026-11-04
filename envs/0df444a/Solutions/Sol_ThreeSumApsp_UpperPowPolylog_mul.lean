-- Prove2me | solution 1 for ThreeSumApsp.UpperPowPolylog.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:10.967411+00:00
-- url     : https://prove2.me/submissions/e1447f22-f29d-47bf-8f7b-6513eeb9b219

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_UpperBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_upperPowPolylog
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono_left
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_exists_isPowPolylog
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_isPowPolylog
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_Dominated_mono_left
import Theorems.Thm_ThreeSumApsp_Dominated_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_isPowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mul
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono_left
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mul


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog
namespace ThreeSumApsp.UpperPowPolylog
theorem _root_.solution (hf : UpperPowPolylog f a) (hg : UpperPowPolylog g b)
    (hg0 : ∀ᶠ n in atTop, 0 ≤ g n) :
    UpperPowPolylog (fun n => f n * g n) (a + b) := by
  obtain ⟨F, -, hF, hfF⟩ := hf.exists_isPowPolylog
  exact (hF.mul (hg.isPowPolylog hg0)).upperPowPolylog.mono_left
    ((hfF.and hg0).mono fun n hn => mul_le_mul_of_nonneg_right hn.1 hn.2)
end ThreeSumApsp.UpperPowPolylog
