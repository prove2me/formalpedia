-- Prove2me | solution 1 for PI.WGL.EqvWt.sum_natW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:22.067959+00:00
-- url     : https://prove2.me/submissions/3bb77724-a39d-4716-a86b-d06baa0c1bf6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
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
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {r : ℕ} (lam : DomWeight r) :
    ((∑ j, lam.natW j : ℕ) : ℤ) = wsum lam - r * lam.detShift := by
  push_cast
  have h : ∀ j : Fin r, ((lam.natW j : ℕ) : ℤ) = lam.w j - lam.detShift := by
    intro j
    have hj := j.isLt
    have hle : lam.detShift ≤ lam.w j := by
      unfold DomWeight.detShift
      rw [dif_pos (by omega : 0 < r)]
      exact lam.anti (Fin.le_iff_val_le_val.mpr (by show j.1 ≤ r - 1; omega))
    unfold DomWeight.natW
    omega
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib]
  simp [wsum]
end PI.WGL.EqvWt
