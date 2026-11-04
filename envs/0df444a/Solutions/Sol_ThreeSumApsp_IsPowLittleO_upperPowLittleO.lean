-- Prove2me | solution 1 for ThreeSumApsp.IsPowLittleO.upperPowLittleO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:12.378895+00:00
-- url     : https://prove2.me/submissions/0dbfee61-8658-4243-98ea-e2f4e3cb66d4

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
namespace ThreeSumApsp
namespace IsPowLittleO
theorem _root_.solution (hf : IsPowLittleO f a) : UpperPowLittleO f a := by
  obtain ⟨ε, hε, hf⟩ := hf
  exact ⟨ε, hε, hf.mono fun n hn => (le_abs_self _).trans hn⟩
end IsPowLittleO
end ThreeSumApsp
