-- Prove2me | solution 1 for PI.FJMA.injB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:17.770876+00:00
-- url     : https://prove2.me/submissions/bd0fe798-fda5-4d06-a09b-75be7229ff8c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMA
open PI.FJM
variable (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
namespace PI.FJMA
theorem _root_.solution : Function.Injective (ιB p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιB, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.rev_inj] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)
end PI.FJMA
