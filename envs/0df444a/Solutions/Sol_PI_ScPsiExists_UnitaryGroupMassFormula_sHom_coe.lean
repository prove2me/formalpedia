-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.sHom_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:40.248744+00:00
-- url     : https://prove2.me/submissions/c8de4058-2a6b-403e-8215-d8328e00c12e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_add_star_eq
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
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (I : AutInst) (x : I.E) :
    ((sHom I x : ℝ) : ℂ) = ∑ v, (I.φ v x + star (I.φ v x)) := by
  simp only [add_star_eq]
  simp [sHom]
end PI.ScPsiExists.UnitaryGroupMassFormula
