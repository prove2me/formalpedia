-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.tT_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:01:43.739914+00:00
-- url     : https://prove2.me/submissions/3727a001-5c11-4eb7-920d-f3392dd02e0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (τ : E →ₗ[F] F) (x : E) (b : Af F) :
    tT τ (x ⊗ₜ b) = algebraMap F (Af F) (τ x) * b := by
  simp [tT, Algebra.smul_def]
end PI.ScPsiExists.UnitaryGroupMassFormula
