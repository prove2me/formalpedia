-- Prove2me | solution 1 for PI.WGL.Adj.detPow_gStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:45.194336+00:00
-- url     : https://prove2.me/submissions/2402732c-3cbf-4a71-af39-fc7b6700be61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_SqActMemNabla
import Theorems.Thm_PI_WGL_Adj_gStar_val
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.Adj
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.Adj
theorem _root_.solution {N : ℕ} (g : GL (Fin N) ℂ) (k : ℤ) :
    detPow ℂ N (gStar g) k = star (detPow ℂ N g k) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, star_zpow₀]
  congr 1
  simp [gStar_val, Matrix.det_conjTranspose]
end PI.WGL.Adj
