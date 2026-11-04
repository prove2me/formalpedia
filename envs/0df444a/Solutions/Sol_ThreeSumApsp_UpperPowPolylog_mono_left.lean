-- Prove2me | solution 1 for ThreeSumApsp.UpperPowPolylog.mono_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:26.741646+00:00
-- url     : https://prove2.me/submissions/ab8c2382-dfcb-4673-9b21-7b1d97d2e1d7

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog
namespace ThreeSumApsp.UpperPowPolylog
theorem _root_.solution (h : UpperPowPolylog f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) :
    UpperPowPolylog f' a := by
  obtain ⟨C, e, hC⟩ := h
  exact ⟨C, e, (hle.and hC).mono fun n hn => hn.1.trans hn.2⟩
end ThreeSumApsp.UpperPowPolylog
