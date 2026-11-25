-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.hform_cT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:00:57.838719+00:00
-- url     : https://prove2.me/submissions/3fac3f65-0556-43f3-aaff-77c23a36cfab

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_eq_dot
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_hform_eq_dot
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
open NumberField Matrix Formalism.UG PI.InHHClassFin
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution {p : Type} [Fintype p] (B : Matrix (Fin I.n) p I.E) (u v : p → I.E) :
    hform (starRingEnd I.E) (cT (starRingEnd I.E) B * I.J * B) u v =
      hform (starRingEnd I.E) I.J (B *ᵥ u) (B *ᵥ v) := by
  rw [hform_eq_dot, hform_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  congr 1
  funext i
  simp [Formalism.UG.cT, vecMul, mulVec, dotProduct, map_sum, mul_comm]
end PI.UnitaryGroupMassFormula.InHHClassFin
