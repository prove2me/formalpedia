-- Prove2me | solution 1 for PI.FJMA.injD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:26.653727+00:00
-- url     : https://prove2.me/submissions/adf449fa-c016-410d-ba02-3ed7e6ecaff5

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
theorem _root_.solution : Function.Injective (ιD p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιD, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.rev_inj] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)
end PI.FJMA
