-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.hform_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:14:27.26892+00:00
-- url     : https://prove2.me/submissions/fe487259-1160-46e8-b358-6ca460cdb214

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
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
theorem _root_.solution (x y : Fin I.n → I.E) :
    hform (starRingEnd I.E) I.J y x = starRingEnd I.E (hform (starRingEnd I.E) I.J x y) := by
  have hJ : ∀ i j, starRingEnd I.E (I.J i j) = I.J j i := by
    intro i j
    have h := congrFun (congrFun I.J_herm j) i
    simpa [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] using h
  simp only [hform, map_sum, map_mul, starRingEnd_self_apply, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end PI.UnitaryGroupMassFormula.InHHClassFin
