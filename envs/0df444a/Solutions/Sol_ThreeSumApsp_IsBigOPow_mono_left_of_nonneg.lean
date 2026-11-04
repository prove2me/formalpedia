-- Prove2me | solution 1 for ThreeSumApsp.IsBigOPow.mono_left_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:23:02.772664+00:00
-- url     : https://prove2.me/submissions/3f380f09-997b-4457-ba6c-a82bcad1639a

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_Dominated_mono_left


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow
namespace ThreeSumApsp.IsBigOPow
theorem _root_.solution (hg : IsBigOPow g a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : IsBigOPow f a :=
  hg.mono_left ((h0.and h).mono fun _ hn => abs_le_abs_of_nonneg hn.1 hn.2)
end ThreeSumApsp.IsBigOPow
