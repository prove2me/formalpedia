-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.hform_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:13.754495+00:00
-- url     : https://prove2.me/submissions/c473d49b-304c-45d4-9b83-791348d75a12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf
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
variable {E : Type} [Field E] [StarRing E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (J : Matrix (Fin n) (Fin n) E) (w z : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J w z = (sv w ᵥ* J) ⬝ᵥ z := by
  unfold Formalism.UG.hform
  simp only [dotProduct, vecMul, sv, Finset.sum_mul]
  exact Finset.sum_comm
end PI.UnitaryGroupMassFormula.LCG
