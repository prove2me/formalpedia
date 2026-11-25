-- Prove2me | solution 1 for P2M_PI_WGL_Adj_nf_sqAct_adj__7005aae57fcc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:06.071068+00:00
-- url     : https://prove2.me/submissions/c6b56fcb-bd52-45b0-b2c6-e31390414781

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_SqActMemNabla
import Theorems.Thm_PI_WGL_Adj_gStar_gStar
import Theorems.Thm_PI_WGL_Adj_nf_sqAct_adj

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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam x (sqAct ℂ N lam g y) = normFock lam (sqAct ℂ N lam (gStar g) x) y := by
  rw [nf_sqAct_adj, gStar_gStar]
end PI.WGL.Adj
