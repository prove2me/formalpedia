-- Prove2me | solution 1 for PI.ScPiFrameW.hJ_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:42.94149+00:00
-- url     : https://prove2.me/submissions/dafe6373-df50-4edf-9490-8f99067762dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Theorems.Thm_PI_ScPiFrameW_hJ_eq_sum
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
namespace PI.ScPiFrameW
theorem _root_.solution (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end PI.ScPiFrameW
