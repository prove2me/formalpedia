-- Prove2me | solution 1 for PI.FJMA.dBA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:34.91968+00:00
-- url     : https://prove2.me/submissions/e9f02490-6d6e-4dd0-a3a3-260ea01aef08

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
theorem _root_.solution : ∀ x, ιB p q r s μ μ' x ∉ Set.range (ιA p q r s μ μ') := by
  rintro x ⟨y, hy⟩
  simp [ιA, ιB] at hy
end PI.FJMA
