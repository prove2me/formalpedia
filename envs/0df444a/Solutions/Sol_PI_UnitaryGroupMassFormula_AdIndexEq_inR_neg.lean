-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.inR_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:47.181899+00:00
-- url     : https://prove2.me/submissions/f4b92286-f958-4314-8a32-6f95d57850d0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v) {z : Av I v}
    (hz : InR I v α z) : InR I v α (-z) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hz
  exact ⟨-a, -b, neg_mem ha, neg_mem hb, by simp only [map_neg]; ring⟩
end PI.UnitaryGroupMassFormula.AdIndexEq
