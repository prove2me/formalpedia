-- Prove2me | solution 1 for PI.WGL.LTE.lam_natW_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:01.036125+00:00
-- url     : https://prove2.me/submissions/750ce8d4-0af5-4548-a24e-0e7b8904c36b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
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
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
namespace PI.WGL.LTE
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (t : ℕ) (ht : t < N) :
    ((lam.natW ⟨t, ht⟩ : ℕ) : ℤ) = lam.w ⟨t, ht⟩ - lam.w ⟨n, by omega⟩ := by
  subst h
  have hds : lam.detShift = lam.w ⟨n, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos (by omega)]
    exact congrArg lam.w (Fin.ext (by simp))
  have hle : lam.w ⟨n, by omega⟩ ≤ lam.w ⟨t, ht⟩ :=
    lam.anti (Fin.le_iff_val_le_val.mpr (by show t ≤ n; omega))
  unfold DomWeight.natW
  rw [hds]
  omega
end PI.WGL.LTE
