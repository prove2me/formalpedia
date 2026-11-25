-- Prove2me | solution 1 for PI.WGL.LTF.bidet_rowW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:08:46.317066+00:00
-- url     : https://prove2.me/submissions/84687111-ea81-4eac-9efb-857281c3f6d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleF
import Theorems.Thm_PI_WGL_LTF_gmin_rowW
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
open PI PI.WGL PI.WGL.LTF
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE
namespace PI.WGL.LTF
theorem _root_.solution {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW n n) (bideterminant ℤ sz hsz I) (tupCnt I) := by
  unfold bideterminant
  have hp := IsWeightedHomogeneous.prod Finset.univ (fun k => initMinor ℤ (n := n) (I k) (hsz k))
    (fun k => ∑ p, (Pi.single (I k p) 1 : Fin n → ℕ)) (fun k _ => gmin_rowW (I k) (Fin.castLE (hsz k)))
  convert hp using 1
  funext a
  simp only [tupCnt, Finset.sum_apply, Pi.single_apply]
  simp [eq_comm]
end PI.WGL.LTF
