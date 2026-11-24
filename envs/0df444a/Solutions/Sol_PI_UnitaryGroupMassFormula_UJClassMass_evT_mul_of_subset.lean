-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.evT_mul_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:58:16.848338+00:00
-- url     : https://prove2.me/submissions/52938875-3c0a-407b-b5ce-19aa16a3c25b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F : Type} [Field F] [NumberField F]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {X Y : Set (HeightOneSpectrum (𝓞 F))} (hXY : X ⊆ Y) : evT X * evT Y = evT X := by
  apply af_ext
  intro u
  rw [af_mul_apply, evT_apply, evT_apply]
  by_cases h : u ∈ X
  · rw [if_pos h, if_pos (hXY h), mul_one]
  · rw [if_neg h, zero_mul]
end PI.UnitaryGroupMassFormula.UJClassMass
