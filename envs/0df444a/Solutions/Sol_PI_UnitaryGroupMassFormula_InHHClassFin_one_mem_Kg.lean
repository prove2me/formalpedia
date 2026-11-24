-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.one_mem_Kg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:13:58.539383+00:00
-- url     : https://prove2.me/submissions/7ec246b7-799a-4a90-b149-5511ee0e9f7c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_OneMemKg
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
open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · show ((1 : I.Gf) : GL (Fin I.n) _) ∈ Formalism.UG.stabGL I.Lf
    simpa using (Formalism.UG.stabGL I.Lf).one_mem
  · simp [Formalism.MainNotions.S.AutInst.fmat]
end PI.UnitaryGroupMassFormula.InHHClassFin
