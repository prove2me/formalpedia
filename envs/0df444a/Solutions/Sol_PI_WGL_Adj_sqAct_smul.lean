-- Prove2me | solution 1 for PI.WGL.Adj.sqAct_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:47.817369+00:00
-- url     : https://prove2.me/submissions/459d4793-30f3-48d0-905b-a9df711ecde2

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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (c : ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g (c • f) = c • sqAct ℂ N lam g f := by
  unfold sqAct
  rw [map_smul, smul_comm]
end PI.WGL.Adj
