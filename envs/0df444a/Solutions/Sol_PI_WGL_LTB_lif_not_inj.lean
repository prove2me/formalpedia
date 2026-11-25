-- Prove2me | solution 1 for PI.WGL.LTB.lif_not_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:05.906316+00:00
-- url     : https://prove2.me/submissions/45eb142f-24bc-4c92-8dd9-565de58a3a95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Theorems.Thm_PI_WGL_LTB_initMinor_not_inj
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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N)
    (hρ : ¬ Function.Injective ρ) : lif h ρ hm = 0 := by
  unfold lif
  refine initMinor_not_inj _ hm (fun hinj => hρ (fun a b hab => ?_))
  have h2 : liftRows h ρ (Fin.castSucc a) = liftRows h ρ (Fin.castSucc b) := by
    simp [liftRows, hab]
  exact Fin.castSucc_inj.mp (hinj h2)
end PI.WGL.LTB
