-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_hform_J__8f64264f3f82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:35:11.450921+00:00
-- url     : https://prove2.me/submissions/ac399a6a-1c0a-48f7-9d0c-877306d78f3c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_cT
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
open NumberField Matrix Formalism.UG PI.InHHClassFin
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
namespace Frame
theorem _root_.solution (fr : Frame I S) (x y : Fin fr.k → I.E) :
    hform (starRingEnd I.E) fr.J' x y =
      hform (starRingEnd I.E) I.J (fr.B *ᵥ Sum.elim 0 x) (fr.B *ᵥ Sum.elim 0 y) := by
  rw [← hform_cT]
  simp only [hform, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  rfl
end Frame
end PI.UnitaryGroupMassFormula.InHHClassFin
