-- Prove2me | solution 1 for PI.WGL.Adj.extremal_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:30.198222+00:00
-- url     : https://prove2.me/submissions/f37c1d87-6c5c-4b6a-a364-ba5ec4c33b2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_SqActMemNabla
import Theorems.Thm_PI_WGL_Adj_natW_anti
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem


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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ∈ nablaSq ℂ N lam :=
  Formalism.GradedWeylDivisibility.hwMem ℂ N N le_rfl lam.natW (natW_anti lam)
end PI.WGL.Adj
