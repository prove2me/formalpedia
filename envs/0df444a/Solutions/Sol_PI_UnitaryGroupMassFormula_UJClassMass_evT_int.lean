-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.evT_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:51:05.32883+00:00
-- url     : https://prove2.me/submissions/6e2d518b-330e-4cf9-bbdd-cc32727d60c0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
open Classical
variable {F : Type} [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (T : Set (HeightOneSpectrum (𝓞 F))) : evT T ∈ intAf F := by
  intro w
  show evT T w ∈ w.adicCompletionIntegers F
  rw [evT_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _
end PI.UnitaryGroupMassFormula.UJClassMass
