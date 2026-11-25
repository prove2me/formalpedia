-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.sgl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:57:24.135719+00:00
-- url     : https://prove2.me/submissions/0ada9551-7bd3-492b-bf98-7b20eb1c434d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt

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
theorem _root_.solution (x y : Fv F v) : sgl v (x * y) = sgl v x * sgl v y := af_ext fun w => by
  rw [af_mul_apply, sgl_apply, sgl_apply, sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, mul_zero]
end PI.UnitaryGroupMassFormula.UJClassMass
