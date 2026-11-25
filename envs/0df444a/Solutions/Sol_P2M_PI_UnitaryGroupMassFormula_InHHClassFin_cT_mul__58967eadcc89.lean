-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_InHHClassFin_cT_mul__58967eadcc89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:37.08682+00:00
-- url     : https://prove2.me/submissions/2e02accb-2b23-4e6e-ae47-e1c3406b8685

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
theorem _root_.solution {m p q : Type} [Fintype p] (M : Matrix m p I.E) (N : Matrix p q I.E) :
    cT (starRingEnd I.E) (M * N) = cT (starRingEnd I.E) N * cT (starRingEnd I.E) M := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
end PI.UnitaryGroupMassFormula.InHHClassFin
