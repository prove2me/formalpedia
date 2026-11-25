-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:42.561971+00:00
-- url     : https://prove2.me/submissions/f00fa361-41bb-4a90-bc61-cb5db2246ffa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosed_inN
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
theorem _root_.solution (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : IsClosed (Ninf I e z) := by
  have h1 : Ninf I e z = ⋂ v, (fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v)) ⁻¹'
      {g | InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) g} := by
    ext s
    simp only [Ninf, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h1]
  exact isClosed_iInter fun v => (isClosed_inN _ _ _).preimage (continuous_uMat_apply I v)
end PI.ScMuExists.UnitaryGroupMassFormula
