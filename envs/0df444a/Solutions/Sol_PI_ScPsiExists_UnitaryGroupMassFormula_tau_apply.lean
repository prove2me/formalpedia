-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:01:29.910124+00:00
-- url     : https://prove2.me/submissions/c5b9383a-57f3-4415-ada1-6a2fbdd0f3b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (x : E) :
    algebraMap F E (tau hfix x) = x + star x :=
  tauFun_spec hfix x
end PI.ScPsiExists.UnitaryGroupMassFormula
