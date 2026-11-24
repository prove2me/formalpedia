-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_AQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:15:45.322915+00:00
-- url     : https://prove2.me/submissions/a8040e6b-b9b7-4dbf-844f-83face809e1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_uMat_mul_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_hP
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) :
    amat I x y v δ * qM I y v = qM I x v * δ.map (I.φ v) := by
  unfold amat qM
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.MainNotions.S.uMat (y.1 v)), ap_uMat_mul_inv, Matrix.one_mul, ap_hP, Matrix.mul_one]
end PI.UnitaryGroupMassFormula.LCG
