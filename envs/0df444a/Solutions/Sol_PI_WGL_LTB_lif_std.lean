-- Prove2me | solution 1 for PI.WGL.LTB.lif_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:07.338797+00:00
-- url     : https://prove2.me/submissions/ca5570ec-92ef-4fd6-9631-75851e9a511c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K)
    (hk : sz k < n) (hm : sz k + 1 ≤ N) :
    lif h (stdT sz hsz k) hm = initMinor ℤ (n := N) (rowsZ h ⟨sz k, hk⟩) hm := by
  unfold lif
  congr 1
  funext p
  simp [liftRows, rowsZ, stdT, eRow]
  have hp := p.2
  split_ifs <;> first | rfl | (exfalso; omega)
end PI.WGL.LTB
