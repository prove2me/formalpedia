-- Prove2me | solution 1 for PI.ScPiFrameW.hJ_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:49.636782+00:00
-- url     : https://prove2.me/submissions/4b280db1-b219-4611-baf9-956b74dc586c

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
    hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ_eq_sum, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end PI.ScPiFrameW
