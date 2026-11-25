-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.algebraMap_O_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:08.243414+00:00
-- url     : https://prove2.me/submissions/45f68128-effc-4fd1-86e2-22e2e9aae526

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField nonZeroDivisors
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField
variable (F : IntermediateField ℚ ℂ)
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (o : 𝓞 F) : algebraMap (𝓞 F) ℂ o = ((algebraMap (𝓞 F) F o : F) : ℂ) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F ℂ]; rfl
end PI.UnitaryGroupMassFormula.UnitDetRoot
