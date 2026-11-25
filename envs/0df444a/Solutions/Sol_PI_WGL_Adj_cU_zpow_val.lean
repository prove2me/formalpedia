-- Prove2me | solution 1 for PI.WGL.Adj.cU_zpow_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:53.950175+00:00
-- url     : https://prove2.me/submissions/7d3b3faf-56b9-470a-84a7-142a9a8c2c2e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_SqActMemNabla

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.Adj
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.Adj
theorem _root_.solution (a : ℂˣ) (e : ℤ) : ((cU a ^ e : ℂˣ) : ℂ) = star ((a ^ e : ℂˣ) : ℂ) := by
  unfold cU
  rw [← map_zpow, Units.coe_map]
  rfl
end PI.WGL.Adj
