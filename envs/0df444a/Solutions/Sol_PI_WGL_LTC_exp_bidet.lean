-- Prove2me | solution 1 for PI.WGL.LTC.exp_bidet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:09.770997+00:00
-- url     : https://prove2.me/submissions/f211833b-b92f-43d4-b0e5-556e218e9f3f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleC
import Theorems.Thm_PI_WGL_LTA_exp_gmin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTC
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM
namespace PI.WGL.LTC
theorem _root_.solution {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K) :
    Exp (id : Fin n → Fin n) (fun ρ : Fin (sz k) → Fin n => initMinor ℤ (n := n) ρ (hsz k)) := exp_gmin id Function.injective_id (Fin.castLE (hsz k))
end PI.WGL.LTC
