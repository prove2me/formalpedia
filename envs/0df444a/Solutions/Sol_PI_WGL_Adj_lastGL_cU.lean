-- Prove2me | solution 1 for PI.WGL.Adj.lastGL_cU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:07:19.63701+00:00
-- url     : https://prove2.me/submissions/47a15a37-f289-4c7b-bfb8-768634591a1a

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
theorem _root_.solution (N : ℕ) (a : ℂˣ) : lastGL ℂ N (cU a) = gStar (lastGL ℂ N a) := by
  ext i j
  simp only [lastGL, diagGL, gStar_val, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp [cU]
  · have hji : j ≠ i := fun e => hij e.symm
    simp [hij, hji]
end PI.WGL.Adj
