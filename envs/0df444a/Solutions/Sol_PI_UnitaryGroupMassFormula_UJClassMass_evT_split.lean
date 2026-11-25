-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.evT_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:33.905612+00:00
-- url     : https://prove2.me/submissions/26b175d3-6ad9-4993-a783-034cafcb0123

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
theorem _root_.solution {B S : Set (HeightOneSpectrum (𝓞 F))} (hBS : B ⊆ S) : evT S = evT B + evT (S \ B) := by
  apply af_ext
  intro u
  rw [af_add_apply, evT_apply, evT_apply, evT_apply]
  by_cases h1 : u ∈ B
  · rw [if_pos (hBS h1), if_pos h1, if_neg (fun h => h.2 h1), add_zero]
  · by_cases h2 : u ∈ S
    · rw [if_pos h2, if_neg h1, if_pos ⟨h2, h1⟩, zero_add]
    · rw [if_neg h2, if_neg h1, if_neg (fun h => h2 h.1), add_zero]
end PI.UnitaryGroupMassFormula.UJClassMass
