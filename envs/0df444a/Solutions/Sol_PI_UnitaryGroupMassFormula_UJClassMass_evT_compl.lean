-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.evT_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:58:16.013292+00:00
-- url     : https://prove2.me/submissions/cb2cdac0-7cab-40b4-aaa2-202265d49fb7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_af_one_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_af_sub_apply
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
theorem _root_.solution (X : Set (HeightOneSpectrum (𝓞 F))) : 1 - evT Xᶜ = evT X := by
  apply af_ext
  intro u
  rw [af_sub_apply, af_one_apply, evT_apply, evT_apply]
  by_cases h : u ∈ X
  · rw [if_neg (fun h' => h' h), if_pos h, sub_zero]
  · rw [if_pos (show u ∈ Xᶜ from h), if_neg h, sub_self]
end PI.UnitaryGroupMassFormula.UJClassMass
