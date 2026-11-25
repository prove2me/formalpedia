-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_DD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:19:05.838767+00:00
-- url     : https://prove2.me/submissions/494b37e8-c898-40f1-b9ae-4acfe73a9ffa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_Jm_herm
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_Jm_sq
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
theorem _root_.solution (y : I.GA) (v : InfinitePlace I.F) {k : ℕ} (b' : Fin k → Fin I.n → I.E) :
    (Formalism.REAL.Jm (I.ε v) * colM I y v b')ᴴ * (Formalism.REAL.Jm (I.ε v) * colM I y v b') =
      (colM I y v b')ᴴ * colM I y v b' := by
  rw [Matrix.conjTranspose_mul, ap_Jm_herm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.REAL.Jm (I.ε v)), ap_Jm_sq, Matrix.one_mul]
end PI.UnitaryGroupMassFormula.LCG
