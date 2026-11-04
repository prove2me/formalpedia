-- Prove2me | solution 1 for ThreeSumApsp.UpperPowLittleO.mono_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:29.690197+00:00
-- url     : https://prove2.me/submissions/5807fcd8-5118-4e4f-ab71-c18a41fcd4df

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
open ThreeSumApsp.UpperPowLittleO
namespace ThreeSumApsp.UpperPowLittleO
theorem _root_.solution (h : UpperPowLittleO f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) :
    UpperPowLittleO f' a := by
  obtain ⟨ε, hε, hf⟩ := h
  exact ⟨ε, hε, (hle.and hf).mono fun n hn => hn.1.trans hn.2⟩
end ThreeSumApsp.UpperPowLittleO
