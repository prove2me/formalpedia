-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.Frame.orth_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:31.558011+00:00
-- url     : https://prove2.me/submissions/560fd613-90d0-46a0-8e3a-ae8f299cc9e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_smul_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_sum_right
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
theorem _root_.solution (fr : Frame I S) (x : Fin fr.k → I.E) :
    ∀ s ∈ S, hform (starRingEnd I.E) I.J s (fr.B *ᵥ Sum.elim 0 x) = 0 := by
  intro s hs
  have e : fr.B *ᵥ Sum.elim 0 x = ∑ b, x b • (fun i => fr.B i (Sum.inr b)) := by
    ext i
    simp [mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_apply, mul_comm]
  rw [e, hform_sum_right]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hform_smul_right, fr.orth s hs b, mul_zero]
end Frame
end PI.UnitaryGroupMassFormula.InHHClassFin
