-- Prove2me | solution 1 for PI.WGL.XiB.eval_initMinor_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:05.21608+00:00
-- url     : https://prove2.me/submissions/cfd47b57-faee-4334-af65-09ab063f8f95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_XiU_det_sub_norm_le_one
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
theorem _root_.solution {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I : Fin s → Fin N) (hI : Function.Injective I) (hs : s ≤ N) :
    ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs)‖ ≤ 1 := by
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det]
  have : (MvPolynomial.eval fun v : Fin N × Fin N => x v.1 v.2).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) =
      Matrix.of fun p q => x (I p) (Fin.castLE hs q) := by
    ext p q; simp
  rw [this]
  exact XiU.det_sub_norm_le_one x hx I (Fin.castLE hs) hI (Fin.castLE_injective hs)
end PI.WGL.XiB
