-- Prove2me | solution 1 for PI.WGL.LTB.tupCnt_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:07.636839+00:00
-- url     : https://prove2.me/submissions/c023f92b-ee36-4b41-beaa-1ddb9f193265

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Theorems.Thm_PI_WGL_LTB_card_eq_val
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
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM
namespace PI.WGL.LTB
theorem _root_.solution {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) : tupCnt (stdT sz hsz) = shapeDeg sz := by
  funext a
  unfold tupCnt shapeDeg
  rw [Finset.card_filter (fun k : Fin K => a.1 < sz k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← card_eq_val (m := sz k) a]
  apply congrArg Finset.card
  ext p
  simp [stdT, Fin.ext_iff]
end PI.WGL.LTB
