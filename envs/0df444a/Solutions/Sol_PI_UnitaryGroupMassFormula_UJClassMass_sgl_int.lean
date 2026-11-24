-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.sgl_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:50.57335+00:00
-- url     : https://prove2.me/submissions/347fcad7-1abb-4341-a99d-5c822145d08c

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
theorem _root_.solution {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : sgl v x ∈ intAf F := by
  intro w
  show sgl v x w ∈ w.adicCompletionIntegers F
  rw [sgl_apply]
  by_cases hw : w = v
  · subst hw; rw [Pi.single_eq_same]; exact hx
  · rw [Pi.single_eq_of_ne hw]; exact zero_mem _
end PI.UnitaryGroupMassFormula.UJClassMass
