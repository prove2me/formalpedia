-- Prove2me | solution 1 for ThreeSumApsp.UpperPowPolylog.isPowPolylog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:43.016002+00:00
-- url     : https://prove2.me/submissions/f350ce03-d334-4c0f-b4d6-a81a97458cc4

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_exists_isPowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left_of_nonneg
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono_left_of_nonneg


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog
namespace ThreeSumApsp.UpperPowPolylog
theorem _root_.solution (h : UpperPowPolylog f a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n) :
    IsPowPolylog f a := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowPolylog
  exact hg.mono_left_of_nonneg h0 hfg
end ThreeSumApsp.UpperPowPolylog
