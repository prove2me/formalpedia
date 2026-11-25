-- Prove2me | solution 1 for PI.WGL.XiB.embGL_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:28.938929+00:00
-- url     : https://prove2.me/submissions/035e45e8-a45e-4128-aabe-9c9c94e04f8b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_XiA_embGL_apply
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
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (t : Fin n → ℂˣ) :
    embGL ℂ n N h (diagGL ℂ n t) = diagGL ℂ N (fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1) := by
  apply Units.ext
  ext a b
  rw [XiA.embGL_apply]
  unfold diagGL
  simp only [Matrix.diagonal_apply]
  by_cases ha : a.1 < n
  · by_cases hb : b.1 < n
    · simp only [ha, hb, dite_true]
      by_cases hab : a = b
      · subst hab
        simp
      · have hab' : (⟨a.1, ha⟩ : Fin n) ≠ ⟨b.1, hb⟩ := fun e => hab (Fin.ext (Fin.mk.inj_iff.mp e))
        simp [hab, hab']
    · have hab : a ≠ b := fun e => hb (e ▸ ha)
      simp [ha, hb, hab]
  · by_cases hb : b.1 < n
    · have hab : a ≠ b := fun e => ha (e ▸ hb)
      simp [ha, hb, hab]
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      simp [ha]
end PI.WGL.XiB
