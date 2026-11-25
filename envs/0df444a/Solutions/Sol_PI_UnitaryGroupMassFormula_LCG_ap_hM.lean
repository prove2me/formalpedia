-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_hM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:36.749287+00:00
-- url     : https://prove2.me/submissions/06c50bf1-1999-4765-b9ae-0d4bd6ee3a62

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
theorem _root_.solution (k : ℕ) (b' : Fin k → Fin I.n → I.E) (w : Fin I.n → I.E) (a : Fin k) :
    (hM I b' *ᵥ w) a = hf I (b' a) w := by
  simp only [hM, hf, Formalism.UG.hform, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply,
    Finset.sum_mul, starRingEnd_apply]
  first
    | exact Finset.sum_comm
    | rw [Finset.sum_comm]
end PI.UnitaryGroupMassFormula.LCG
