-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Hset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:36:11.838851+00:00
-- url     : https://prove2.me/submissions/c9eba193-ebb0-4f02-9f99-891c191795bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_continuous_uMat_apply
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
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
variable {r : ℕ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (S : Set (Fin I.n → I.E)) : IsClosed (Hset I S) := by
  have h1 : Hset I S = ⋂ v, ⋂ x ∈ S, {s : I.Ginf | Formalism.MainNotions.S.uMat (s v) *ᵥ rv I v x = rv I v x} := by
    ext s
    simp only [Hset, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h1]
  refine isClosed_iInter fun v => isClosed_biInter fun x _ => ?_
  exact isClosed_eq ((continuous_uMat_apply I v).matrix_mulVec continuous_const) continuous_const
end PI.ScMuExists.UnitaryGroupMassFormula
