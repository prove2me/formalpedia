-- Prove2me | solution 1 for PI.WGL.LTC.rowGen_gmin_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:51:41.376976+00:00
-- url     : https://prove2.me/submissions/6015d934-f6ef-45f5-aea5-f338a5b82d46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleC
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_LTA_rowGen_gmin
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
open PI PI.WGL PI.WGL.LTC
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM
namespace PI.WGL.LTC
theorem _root_.solution {r c m : ℕ} (a b : Fin r) (hab : a ≠ b) (ρ : Fin m → Fin r) (κ : Fin m → Fin c)
    (hρ : (∃ pa, ρ pa = a) ∨ ∀ p, ρ p ≠ b) :
    rowGen ℤ a b (gmin ρ κ) = Polynomial.C (gmin ρ κ) := by
  classical
  rw [rowGen_gmin, Finset.sum_eq_single ∅]
  · have hu : upd ρ ∅ a = ρ := by
      funext p
      simp [upd]
    simp [hu]
  · intro S _ hS
    split_ifs with hc
    · obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      rcases hρ with ⟨pa, hpa⟩ | hρ
      · have hne : pa ≠ p0 := by
          intro h
          apply hab
          rw [← hpa, h]
          exact hc p0 hp0
        have hpaS : pa ∉ S := fun h => hab (hpa.symm.trans (hc pa h))
        have hz : gmin (upd ρ S a) κ = 0 := by
          unfold gmin
          apply Matrix.det_zero_of_row_eq hne
          funext q
          simp [upd, hpaS, hp0, hpa]
        simp [hz]
      · exact absurd (hc p0 hp0) (hρ p0)
    · rfl
  · simp
end PI.WGL.LTC
