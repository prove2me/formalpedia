-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fsLog_le_a8984c2e2088
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:02.689799+00:00
-- url     : https://prove2.me/submissions/8ffa5776-f2df-470f-b7b9-81e60f293495

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_norm_pairing_le_f1169a0aed31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) {u y : Fin n → ℂ} (hy : ∑ j, u j * y j ≠ 0) :
    fsLog h u y ≤ Real.log (h.norm u) := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hd := h.dualNorm_pos hy0
  have hnum : 0 < ‖∑ j, u j * y j‖ := norm_pos_iff.mpr hy
  unfold fsLog
  apply Real.log_le_log (div_pos hnum hd)
  rw [div_le_iff₀ hd]
  exact h.norm_pairing_le u y
end GroundTheory.Heights₂.Heights
