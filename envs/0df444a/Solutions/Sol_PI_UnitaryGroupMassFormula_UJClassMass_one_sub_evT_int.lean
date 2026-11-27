-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.one_sub_evT_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:42.246802+00:00
-- url     : https://prove2.me/submissions/b9c47343-8514-4875-a235-cecd3229533b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_af_sub_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_af_one_apply
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
theorem _root_.solution (T : Set (HeightOneSpectrum (𝓞 F))) : 1 - evT T ∈ intAf F := by
  intro w
  show (1 - evT T) w ∈ w.adicCompletionIntegers F
  rw [af_sub_apply, evT_apply, af_one_apply]; split_ifs
  · rw [sub_self]; exact zero_mem _
  · rw [sub_zero]; exact one_mem _
end PI.UnitaryGroupMassFormula.UJClassMass
