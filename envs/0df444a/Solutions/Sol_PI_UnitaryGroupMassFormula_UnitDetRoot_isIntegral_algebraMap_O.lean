-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.isIntegral_algebraMap_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:23.044222+00:00
-- url     : https://prove2.me/submissions/924460b1-56aa-4ad8-922a-3b334fe28266

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (F : IntermediateField ℚ ℂ) (o : 𝓞 F) :
    IsIntegral ℤ (algebraMap (𝓞 F) ℂ o) := by
  first
    | exact (NumberField.RingOfIntegers.isIntegral o).algebraMap
    | exact IsIntegral.algebraMap o.isIntegral_coe
    | exact (o.isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F ℂ)
end PI.UnitaryGroupMassFormula.UnitDetRoot
