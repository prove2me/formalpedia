-- Prove2me | solution 1 for ThreeSumApsp.isPowLittleO_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:38.001207+00:00
-- url     : https://prove2.me/submissions/03e2cb73-4544-45af-8015-e11f98e358d1

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_eventually_abs_le
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_of_eventually_abs_le
import Theorems.Thm_ThreeSumApsp_Dominated_mono_left
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_IsBigOPow_eventually_abs_le
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_eventually_abs_le
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono_left
import Theorems.Thm_ThreeSumApsp_isBigOPow_rpow


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
theorem _root_.solution : IsPowLittleO f a ↔ ∀ η : ℝ, 0 < η → IsBigOPow f (a + η) :=
  ⟨fun h η hη => (isBigOPow_rpow (a + η)).mono_left
      ((h.eventually_abs_le (lt_add_of_pos_right a hη)).mono
        fun _ hfn => hfn.trans (le_abs_self _)),
    fun h => .of_eventually_abs_le fun η hη =>
      (h (η / 2) (half_pos hη)).eventually_abs_le (by linarith)⟩
end ThreeSumApsp
