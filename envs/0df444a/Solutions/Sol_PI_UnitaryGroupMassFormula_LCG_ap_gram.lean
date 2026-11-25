-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:25.775694+00:00
-- url     : https://prove2.me/submissions/d9d14662-2191-4228-adec-8b47b982a3d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
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
theorem _root_.solution (z : I.GA) (v : InfinitePlace I.F) {k : ℕ} (b : Fin k → Fin I.n → I.E) :
    PI.LatCountG.gramV I z v b = (colM I z v b)ᴴ * colM I z v b := by
  ext a c
  simp [PI.LatCountG.gramV, colM, Matrix.mul_apply, Matrix.conjTranspose_apply]
end PI.UnitaryGroupMassFormula.LCG
